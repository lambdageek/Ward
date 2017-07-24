{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Check.Permissions
  ( Function(..)
  -- * Analysis entry points
  , process
  , validatePermissions
  -- * Transfer functions
  , strongUpdateCap
  , transferNewNonConflicting
  ) where

import Algebra.Algebra
import Config
import Control.Monad (unless, when)
import Control.Monad.IO.Class (liftIO)
import Data.Foldable (for_, toList)
import Data.Function (fix)
import Data.Graph (Graph, graphFromEdges)
import Data.IORef
import Data.List (isSuffixOf, nub, sort)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>), Any(..))
import Data.These
import Data.Vector.Mutable (IOVector)
import Language.C.Data.Ident (Ident)
import Language.C.Data.Node (NodeInfo, posOfNode)
import Language.C.Data.Position (posFile)
import Types
import qualified Data.Graph as Graph
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Data.Tree as Tree
import qualified Data.Vector as Vector
import qualified Data.Vector.Mutable as IOVector

-- | A function given as input to the permission checking algorithm.
data Function = Function
  {
  -- | The source location where the function was declared, or where it was
  -- defined if there was no declaration.
    functionPos :: !NodeInfo

  -- | The name of the function, prefixed with its file path if @static@.
  , functionName :: !FunctionName

  -- | The permission actions declared for this function in the source file.
  , functionPermissions :: !PermissionActionSet

  -- | A tree of callees of this function.
  , functionCalls :: !(CallSequence FunctionName)
  }

-- | A node in the call graph, representing a function and information about
-- permissions at each of its call sites.
data Node = Node
  {
  -- | The permission actions of the function. This is set in the initial state
  -- by annotations, and updated as permissions are propagated.
    nodePermissions :: !(IORef PermissionActionSet)

  -- | The initial annotated permission actions of the function.
  , nodeAnnotations :: !PermissionActionSet

  -- | The callees of this function.
  , nodeCalls :: !(CallSequence FunctionName)

  -- | The permission states inferred as the pre- and post- conditions of this function, from its callees.
  , nodeSitePre :: !(IORef Site)
  , nodeSitePost :: !(IORef Site)

  -- | The original name of this function, for error reporting.
  , nodeName :: !FunctionName

  -- | The original source location of this function, for error reporting.
  , nodePos :: !NodeInfo
  }

-- | A call 'Site' is represented by a set of 'PermissionPresence's, describing
-- which permissions are available ('Has'), needed ('Uses'), unavailable
-- ('Lacks'), or have conflicting information ('Conflicts') at each call site
-- within each function.
type Site = PermissionPresenceSet

-- | 'process' infers permissions for a call graph specified by a list of
-- 'Function's and verifies their consistency and correctness according to a
-- 'Config'.
--
-- The permission checking algorithm is fairly straightforward. We are given a
-- set of functions; each function has some associated permission actions and a
-- tree of calls to other functions.
--
-- > // Input
-- >
-- > void begin  () __attribute__ ((ward (grant  (perm))));
-- > void end    () __attribute__ ((ward (revoke (perm))));
-- > void truthy () __attribute__ ((ward (need   (perm))));
-- > void falsy  () __attribute__ ((ward (need   (perm))));
-- >
-- > void outer () {
-- >   if (begin ()) {
-- >     truthy ();
-- >   } else {
-- >     falsy ();
-- >   }
-- >   end ();
-- > }
--
-- > // Call tree
-- > begin = end = truthy = falsy = nop
-- > outer = begin & (truthy | falsy) & end
--
-- We take the top-level 'Sequence' of a call tree and flatten it into a vector
-- of call 'Site' info, initially empty. Each cell represents the state /before/
-- and /after/ a call, so there is one more 'Site' than calls in the tree.
--
-- > outer = [ {}  -- state before 'begin'
-- >               -- call to 'begin'
-- >         , {}  -- state after 'begin', before 'if'
-- >               -- 'if'
-- >         , {}  -- state after 'if', before 'end'
-- >               -- call to 'end'
-- >         , {}  -- state after 'end'
-- >         ]
--
-- For each call in the tree, we add information to the 'Site' before and after
-- the call according to the callee's permission actions. After one step the
-- state looks like this:
--
-- > outer = [ {lacks(perm)}  -- 'perm' can't already be in the context because...
-- >                          -- ...'begin' grants 'perm'...
-- >         , {has(perm)}    -- ...after which 'perm' is in the context.
-- >         , {}
-- >         , {}
-- >         ]
--
-- When we reach a 'Choice', we create a new sub-vector for each branch of the
-- 'Choice' and check its 'Sequence' of calls recursively in the same way as
-- the top-level sequence.
--
-- Creating the vectors:
--
-- > choice-A = [ {}  -- state before 'truthy'
-- >                  -- call to 'truthy'
-- >            , {}  -- state after 'truthy'
-- >            ]
-- >
-- > choice-B = [ {}  -- state before 'falsy'
-- >                  -- call to 'falsy'
-- >            , {}  -- state after 'falsy'
-- >            ]
--
-- Filling them in:
--
-- > choice-A = [ {has(perm)}  -- 'perm' must be in the context because...
-- >                           -- ...'truthy' needs 'perm'...
-- >            , {has(perm)}  -- ...and doesn't change the context.
-- >            ]
-- >
-- > choice-B = [ {has(perm)}  -- 'perm' must be in the context because...
-- >                           -- ...'falsy' needs 'perm'...
-- >            , {has(perm)}  -- ...and doesn't change the context.
-- >            ]
--
-- We then merge the effects of the branches of the choice, and treat it as a
-- single call, discarding the sub-vectors.
--
-- > outer = [ {lacks(perm)}
-- >         , {has(perm)}   -- 'perm' was already in the context...
-- >         , {has(perm)}   -- ...and the 'if' doesn't change that.
-- >         , {}
-- >         ]
--
-- After that, we can return up a level, and continue processing the rest of the
-- sequence we came from.
--
-- > outer = [ {lacks(perm)}
-- >         , {has(perm)}
-- >         , {has(perm)}    -- 'perm' must already be in the context because...
-- >                          -- ...'end' revokes 'perm'...
-- >         , {lacks(perm)}  -- ...after which 'perm' is not in the context.
-- >         ]
--
-- (This omits the details of how permissions are /propagated/ through a
-- function and between functions, which are explained inline.)
--
-- From the initial and final call sites of this sequence, we can deduce the
-- permission actions of the whole function. This is a trivial example: the net
-- effect of the function is @{lacks(perm)} -> {lacks(perm)}@, from which we
-- deduce no permission actions; @outer@ uses @perm@ entirely locally, so it
-- requires no annotations.
--
-- Things become more interesting when accounting for more complex uses of
-- permissions, as well as permission errors. This is the whole point of Ward:
-- to report inconsistencies and violations of assertions to help catch bugs.
--
-- After permission information has been inferred for all call sites in the call
-- graph, we check the result for consistency and report errors.
--
-- The first and most basic form of error is a /conflict/: when we infer that a
-- call site both @has@ and @lacks@ a permission, we know that someone must be
-- using permissions incorrectly. For example, if we called @begin@ twice in the
-- example above, we would have this call tree:
--
-- > outer = begin & begin & ...
--
-- We would start by inferring @{lacks(perm)} -> {has(perm)}@ for the first call
-- to @begin@:
--
-- > outer = [ {lacks(perm)}
-- >         , {has(perm)}
-- >         , {}
-- >         ...
-- >         ]
--
-- But for the second call, we would also infer @{lacks(perm)} -> {has(perm)}@:
--
-- > outer = [ {lacks(perm)}
-- >         , {has(perm),lacks(perm)}  -- Conflict!
-- >         , {has(perm)}
-- >         ...
-- >         ]
--
-- Whenever we would infer @{has(p),lacks(p)}@ for some permission @p@, we
-- replace it with @{conflicts(p)}@ to record the conflict. This ensures that we
-- don't continue to propagate any inconsistent permission information, so we
-- can avoid reporting many redundant errors.
--
-- The other forms of errors come from /restrictions/ and /enforcements/.
--
-- Restrictions describe relationships between permissions. If a call site
-- /uses/ a permission that has a restriction, then we evaluate the
-- corresponding expression on the context and report an error if it's false.
--
-- Enforcements describe which functions must be annotated. If a function
-- matches an enforcement (by path or name), then we report any permission
-- actions that were inferred but not specified in an annotation.
--
process :: [Function] -> Config -> Logger ()
process functions config = do

  -- We find all functions that require annotations according to enforcements in
  -- the config, and collect their annotations for checking later.
  let
    requiresAnnotation :: FunctionName -> NodeInfo -> Bool
    requiresAnnotation name info = or
      [ case enforcement of
        This path' -> path' `isSuffixOf` path
        That name' -> name == name'
        These path' name' -> path' `isSuffixOf` path && name == name'
      | enforcement <- configEnforcements config
      ]
      where
        path = posFile $ posOfNode info

    requiredAnnotations :: [(FunctionName, PermissionActionSet)]
    requiredAnnotations = 
      [ (name, permissions)
      | Function
        { functionName = name
        , functionPos = info
        , functionPermissions = permissions
        } <- functions
      , requiresAnnotation name info
      ]

    restrictions =
      [ Restriction
        { restName = name
        , restExpression = expr
        , restDescription = desc
        }
      | (name, decl) <- Map.toList $ configDeclarations config
      , (expr, desc) <- declRestrictions decl
      ]

  -- Next, we build the call graph, transpose it to obtain a callee graph, and
  -- partition it into strongly connected components (SCCs), which we check in
  -- dependency order. This is how we propagate permission information between
  -- functions.

  edges <- liftIO $ edgesFromFunctions functions
  let
    callerGraph :: Graph
    graphLookup :: Graph.Vertex -> (Node, FunctionName, [FunctionName])
    graphVertex :: FunctionName -> Maybe Graph.Vertex
    (callerGraph, graphLookup, graphVertex) = graphFromEdges edges

    calleeGraph :: Graph
    calleeGraph = Graph.transposeG callerGraph

    topologicallySorted = Graph.topSort calleeGraph
    sccs = Graph.dfs calleeGraph topologicallySorted

    -- All functions are implicitly annotated with all permissions that are
    -- declared "implicit" in the config, unless waived by an annotation.
    implicitPermissions :: [PermissionName]
    implicitPermissions =
      [ name
      | (name, decl) <- Map.toList $ configDeclarations config
      , declImplicit decl
      ]

  -- Then we propagate permission information through the graph.

  -- For each SCC:
  liftIO $ for_ sccs $ inferPermissionsSCC implicitPermissions graphLookup graphVertex

  -- Finally, we check the whole call graph, reporting conflicting information
  -- at call sites, missing annotations (from enforcements), and violated
  -- restrictions.

  for_ sccs $ reportSCC requiredAnnotations restrictions graphLookup

  -- That's all, folks!

----------------------------------------------------------------------
-- Inference
----------------------------------------------------------------------

inferPermissionsSCC :: [PermissionName]
           -> (Graph.Vertex -> (Node, FunctionName, [FunctionName]))
           -> (FunctionName -> Maybe Graph.Vertex)
           -> Tree.Tree Graph.Vertex
           -> IO ()
inferPermissionsSCC implicitPermissions graphLookup graphVertex scc = do
    -- We continue processing until the SCC's permission information reaches a
    -- fixed point, i.e., we are no longer adding permission information.
    growing <- newIORef mempty
    fix $ \ loop -> do
      writeIORef growing mempty

      -- For each function in the SCC:
      for_ scc $ \ vertex -> do
        let
          (node, name, _incoming) = graphLookup vertex
        -- For each permission action in function, plus implicit permissions not waived:
        permissionActions <- readIORef $ nodePermissions node
        let
          implicitPermissionActions =
            [ Need p
            | p <- implicitPermissions
            , not $ Waive p `HashSet.member` permissionActions
            ]
          nodePermissionActions = HashSet.toList permissionActions <> implicitPermissionActions

        nodeGrowing <- propagatePermissionsNode graphLookup (nodeSitePre node, nodeSitePost node, nodePermissions node, initialSite nodePermissionActions, name, graphVertex <$> nodeCalls node)
        modifyIORef' growing (<> nodeGrowing)

      -- We continue processing the current SCC if we're still propagating
      -- permission information between functions.
      do
        shouldContinue <- readIORef growing
        if getAny shouldContinue then loop else pure ()

propagatePermissionsNode :: (Graph.Vertex -> (Node, t1, t))
                       -> (IORef Site, IORef Site, IORef PermissionActionSet, Site, FunctionName, CallSequence (Maybe Graph.Vertex))
                       -> IO Any
propagatePermissionsNode graphLookup (sitePre, sitePost, permissionsRef, newInitialSite, name, callVertices) = do
        -- We initialize the first call site of the function according to its
        -- permission actions.
        modifyIORef' sitePre (\old -> old \/ newInitialSite)

        let
          graphLookup' :: Graph.Vertex -> IO PermissionActionSet
          graphLookup' call =  do
            let (Node { nodePermissions = callPermissionsRef }, _callName, _) = graphLookup call
            readIORef callPermissionsRef
        -- replace each Graph.Vertex by its current PermissionActionSet
        --
        -- callPermissions :: CallSequence (Maybe PermissionActionSet)
        callPermissions <- traverse (traverse graphLookup') callVertices
        -- Next, we infer information about permissions at each call site in the
        -- function by traversing its call tree.
        -- We start processing the call tree from the root, filling in the list
        -- of top-level call sites for the function.
        initialPre <- readIORef sitePre
        initialPost <- readIORef sitePost
        (finalPre, finalPost) <- processCallSequence callPermissions (initialPre,initialPost)
        writeIORef sitePre finalPre
        writeIORef sitePost finalPost
        writePermissionsFromInferred permissionsRef (finalPre, finalPost)


processCallSequence :: Monad m =>
                       CallSequence (Maybe PermissionActionSet)
                    -> (Site, Site)
                    -> m (Site, Site)
processCallSequence s (initialPre, initialPost) =
  case viewlCallSequence s of
    Just (a,b) -> do
            (fwdPre, fstMid) <- processCallTree a (initialPre, bottom)
            (fwdMid, finalPost) <- processCallSequence b (fstMid, initialPost)

            -- Once we've collected permission information for each call site
            -- and propagated it forward, we propagate all new or /newly-conflicting/
            -- information /backward/ through the whole sequence; this has the
            -- effect of filling in the 0th call site (before the first call) in
            -- a function with any relevant permissions from the body of the
            -- function.
            let
              update before after = transferNewNonConflicting after before
              finalMid = update fwdMid finalPost
              finalPre = update fwdPre finalMid
            finalPre `seq` return (finalPre, finalPost)
    Nothing -> pure (initialPre, initialPost)

-- | Given the permissions after a call-site, update the permissions prior to
-- the call-site by incorporating any new information, or /new/ conflicts from
-- after the call.
transferNewNonConflicting :: PermissionPresenceSet -> PermissionPresenceSet -> PermissionPresenceSet
transferNewNonConflicting after before =
  before \/ permissionDiff after before
  where
    permissionDiff (PermissionPresenceSet x) (PermissionPresenceSet y) =
      PermissionPresenceSet (HashMap.differenceWith keepConflicting x y)
    keepConflicting pafter _pbefore =
      if conflicting pafter then Just pafter else Nothing

-- | Given a call tree and the permission presence set at the current site (as
-- an index into a vector of sites), update the current site and the following one
-- with the new permission presence set.
processCallTree :: Monad m =>
                   CallTree (Maybe PermissionActionSet)         -- input
                -> (Site, Site)        -- permissions prior and after this calltree
                -> m (Site, Site)
processCallTree (Choice a b) (initialPre, initialPost) = do
            (beforeA, afterA) <- processCallSequence a bottom
            (beforeB, afterB) <- processCallSequence b bottom
            let
              finalPre = initialPre \/ beforeA \/ beforeB
              finalPost = initialPost \/ afterA \/ afterB
            finalPre `seq` finalPost `seq` return (finalPre, finalPost)

processCallTree (Call (Just callPermissions)) initialPrePost =
  pure (processKnownCall callPermissions initialPrePost)

processCallTree (Call Nothing) initialPrePost =
                -- Assume an unknown call has irrelevant permissions. I just know this
                -- is going to bite me later.
                pure initialPrePost


-- | Given a known call with the given permission action set, and the initial sites prior to and after the call node,
-- return the updated call sites prior to and after the call taking into account the given permission actions.
processKnownCall :: PermissionActionSet -> (Site, Site) -> (Site, Site)
processKnownCall callPermissions (initialPre, initialPost) =
            -- We propagate permissions forward in the call tree
            -- at each step. This ensures that the /final/ call site (after the
            -- last call) contains relevant permissions from the body of the
            -- function.
            let
              fwdPost = initialPre \/ initialPost

              -- Update permission presence (has/lacks/conflicts) according to
              -- permission actions (needs/denies/grants/revokes).
              finalPre = initialPre \/ getJoin (foldMap actionPrecondition callPermissions)
              finalPost = HashSet.foldl' updatePost fwdPost callPermissions
            in finalPre `seq` finalPost `seq` (finalPre, finalPost)

  -- Note how this works with the forward-propagation above: if a call
  -- site grants or revokes a permission for which information was
  -- propagated from the previous call site, the old information is
  -- /replaced/ to indicate the change in permissions; it doesn't
  -- generate a conflict unless there's actually conflicting info. And
  -- if some permission is irrelevant to a particular call, it just
  -- passes on through.
  where
    updatePost :: Site -> PermissionAction -> Site
    updatePost = flip strongUpdateCap

strongUpdateCap :: PermissionAction -> PermissionPresenceSet -> PermissionPresenceSet
strongUpdateCap act =
  let
    pn = permissionActionName act
  in modifyPresence pn update
  where
    -- FIXME: this _appears_ to depend on the order of PermissionActions
    -- (because 'dropCapability' will bottom-out a preceeding update to the
    -- same permission name), but actually since the only actions that have
    -- non-bottom postconditions are @Grant pn@ and @Revoke pn@ (and a single
    -- grant/revoke for the same permission are mutually exclusive, the order
    -- of updates doesn't matter).  It would be better if 'PermissionAction'
    -- made this mutual-exclusivity explicit.
    update old = dropCapability old \/ actionPostcondition act
     -- uses = (Uses, CapUnknown) so the effect of dropCapability is to leave
     -- Usage unchanged and cut Capability back down to CapUnknown
    dropCapability x = x /\ uses

-- After processing a call tree, write back its updated permission actions
-- based on the permissions inferred before the first and after the last call
-- sites.  Returns @Any True@ if the permissions changed since the last
-- iteration, or @Any False@ if they stayed the same.
writePermissionsFromInferred :: IORef PermissionActionSet -> (Site, Site) -> IO Any
writePermissionsFromInferred permissionRef initialFinal@(initial, final) = do
            initialActions <- readIORef permissionRef
            let (finalActions, change) = updatePermissionActions initialActions initialFinal
            writeIORef permissionRef finalActions
            -- TODO: Limit the number of iterations to prevent infinite loops.
            return change

-- | Given the previous 'PermissionActionSet' of a call, and newly inferred
-- permissons at the initial and final site in the function (before the first
-- call, after the final call), compute the updated permission action set and a flag
-- indicating if any new permissions were added.
updatePermissionActions :: PermissionActionSet -> (Site, Site) -> (PermissionActionSet, Any)
updatePermissionActions initialActions initialFinal@(initial,final) =
            let
              currentSize = HashSet.size initialActions

              -- For each "relevant" permission P in first & last call sites:
              relevantPermissions = presenceKeys (initial \/ final)

              derivedActions = HashSet.fromList $ mconcat $ map (derivePermissionActions initialFinal) relevantPermissions
              finalActions = derivedActions <> initialActions

              modifiedSize = HashSet.size finalActions

              -- If we added permissions, the inferred set of permissions for this
              -- SCC may still be growing, so we re-process the SCC until we reach a
              -- fixed point.
              change = (modifiedSize /= currentSize) || (finalActions /= initialActions)

              -- FIXME: At this point it maybe useful to compute another piece
              -- of information: a set of PermissionNames that are mapped to
              -- 'CapConflict' by the initial or final 'Site'.  The reason is
              -- because in some sense PermissionActionSet is a summary of the
              -- information we can glean from @(initial,final)@.  If
              -- 'PermissionActionSet' was isomorphic to @(Site,Site)@, we
              -- could throw the 'Site's away between iterations.  But the pair
              -- of sites has additional information - precisely the conflicts!
              -- (Also I think @('Uses', 'CapLacks')@ is not representable, by
              -- a 'PermissionAction', which is a shame).
            in change `seq` (finalActions, Any change)

-- Given the initial and final call sites and a permission P, determine the action
-- of the function with respect to P by considering its presence or absence at function entry and exit.
derivePermissionActions :: (Site,Site) -> PermissionName -> [PermissionAction]
derivePermissionActions (initial,final) p =
  needsRevokes <> grants
  where
    -- (NB. The seemingly redundant side conditions here prevent spurious
    -- error messages from inconsistent permissions.)
    needsRevokes =
      if (has `leq` lookupPresence p initial && not (lacks `leq` lookupPresence p initial))
      then -- When the initial state has P, the function needs P.
        needs <> revokes
      else
        mempty
    grants =
      if (lacks `leq` lookupPresence p initial && not (has `leq` lookupPresence p initial))
         && (has `leq` lookupPresence p final && not (lacks `leq` lookupPresence p final))
      then
        -- When the initial state lacks P but the final state has P, the
        -- function grants P.
        [Grant p]
      else
        mempty

    needs = [Need p]
    revokes =
      if (lacks `leq` lookupPresence p final && not (has `leq` lookupPresence p final))
      then 
        -- When the initial state has P, but the final state lacks P,
        -- the function revokes P.
        [Revoke p]
      else
        mempty


----------------------------------------------------------------------
-- Reporting
----------------------------------------------------------------------


reportSCC :: [(FunctionName, PermissionActionSet)]
          -> [Restriction]
          -> (Graph.Vertex -> (Node, FunctionName, [FunctionName]))
          -> Tree.Tree Graph.Vertex
          -> Logger ()
reportSCC requiredAnnotations restrictions graphLookup scc = do
  -- For each function in each SCC:
    for_ scc $ \vertex -> do
      let
        (node, _name, _incoming) = graphLookup vertex
        name = nodeName node
        pos = nodePos node
        requiredPermissions = lookup name requiredAnnotations
        annotations = nodeAnnotations node

      permissions <- liftIO $ readIORef $ nodePermissions node
      reportDefinition restrictions requiredPermissions (annotations, permissions, name, pos)

      (sitePre, sitePost) <- liftIO ((,) <$> readIORef (nodeSitePre node) <*> readIORef (nodeSitePost node) )
      reportCallSites restrictions (sitePre, sitePost, nodeCalls node, name, pos)


-- | Report violations at the function definitino due to missing required annotations,
-- annotations that miss inferred permissions, or inconsistent inferred permissions.
reportDefinition :: [Restriction]
           -> Maybe PermissionActionSet
           -> (PermissionActionSet, PermissionActionSet, FunctionName, NodeInfo)
           -> Logger ()
reportDefinition restrictions requiredPermissions (annotations, permissions, name, pos) = do
      -- If a function has required annotations, ensure the annotation
      -- mentions all inferred permissions.
      for_ requiredPermissions $ \ userAnnotated -> do
        -- I think this should generally be equal to 'inferredNotDeclared'.
        let implicit = HashSet.difference permissions userAnnotated
        unless (HashSet.null implicit) $ do
          record True $ Error pos $ Text.concat
            [ "missing required annotation on '"
            , name
            , "'; annotation "
            , Text.pack $ show $ HashSet.toList userAnnotated
            , " is missing: "
            , Text.pack $ show $ HashSet.toList implicit
            ]

      -- If a function has annotations...
      unless (HashSet.null annotations) $ do
        let inferredNotDeclared = HashSet.difference permissions annotations

        -- ...then those annotations must mention all inferred permissions.
        unless (HashSet.null inferredNotDeclared) $ do
          record True $ Error pos $ Text.concat
            [ "annotation on '"
            , name
            , "' is missing these permissions: "
            , Text.pack $ show $ HashSet.toList inferredNotDeclared
            ]

        -- Likewise, the inferred permission actions must be consistent with the
        -- declared permission actions.
        for_ (HashSet.toList permissions) $ \ permission -> do
          let
            mInconsistency = case permission of
              Need p
                | Grant p `HashSet.member` permissions
                -> Just (Grant p)
              Grant p
                | Revoke p `HashSet.member` permissions
                -> Just (Revoke p)
              _ -> Nothing
          flip (maybe (pure ())) mInconsistency $ \ inconsistency -> do
            record True $ Error pos $ Text.concat
              [ "inferred inconsistent permissions for '"
              , name
              , "': "
              , Text.pack $ show permission
              , " is incompatible with "
              , Text.pack $ show inconsistency
              ]

-- | Report violations at the calls in the given function due to
-- callee functions with conflicting permissions or violated restrictions.
reportCallSites :: [Restriction]
                -> (Site, Site, CallSequence FunctionName, FunctionName, NodeInfo)
                -> Logger ()
reportCallSites restrictions (sitePre, sitePost, callees, name, pos) = do
      -- Report call sites with conflicting information.
      let conflicts = conflictingPresence sitePre \/ conflictingPresence sitePost
      unless (nullPresence conflicts) $ do
        record True $ Error pos $ Text.concat $
          [ "conflicting information for permissions "
          , Text.pack $ show $ presenceKeys conflicts
          , " in '"
          , name
          , "'"
          ]

      -- FIXME: need to re-compute the intermediate sites and check their restrictions

      -- For each call site, check every restriction and report any violations.
      for_ (zip [0 :: Int ..] [sitePre,sitePost]) $ \ (index, s) -> do
        let
          position = case index of
            0 -> ["before first call"]
            _ ->
              [ "at "
              , Text.pack $ show $ callTreeIndex (index - 1) callees
              ]
        for_ restrictions $ \ restriction -> do
          unless (evalRestriction s restriction) $ do
            record True $ Error pos $ Text.concat $
              [ "restriction "
              , Text.pack $ show restriction
              , " violated in '"
              , name
              {-
              , "' with permissions '"
              , Text.pack $ show $ HashSet.toList s
              -}
              , "' "
              ]
              <> position


-- | Builds call graph edges from a list of functions, for input to
-- @Data.Graph.graphFromEdges@.
edgesFromFunctions :: [Function] -> IO [(Node, FunctionName, [FunctionName])]
edgesFromFunctions functions = do
  result <- newIORef []
  for_ functions $ \ function -> do
    let name = functionName function
    permissions <- newIORef $ functionPermissions function
    sitePre <- newIORef bottom
    sitePost <- newIORef bottom
    let
      annotations = functionPermissions function
      node =
        ( Node
          { nodePermissions = permissions
          , nodeAnnotations = annotations
          , nodeCalls = functionCalls function
          , nodeSitePre = sitePre
          , nodeSitePost = sitePost
          , nodeName = name
          , nodePos = functionPos function
          }
        , name
        , toList $ functionCalls function
        )
    modifyIORef' result (node :)
  readIORef result

-- | Evaluates a restriction in a context.
evalRestriction :: PermissionPresenceSet -> Restriction -> Bool
evalRestriction context restriction
  | uses `leq` lookupPresence (restName restriction) context = go $ restExpression restriction -- FIXME: what if the context lacks the given restriction or uses it? ignore?
  | otherwise = True
  where
    go = \ case
      -- Since 'Conflicts' represents both 'Has' and 'Lacks', it matches both.
      Context pn pval -> pval `leq` lookupPresence pn context
      a `And` b -> go a && go b
      a `Or` b -> go a || go b
      Not a -> not $ go a

validatePermissionActionSet :: Config -> PermissionActionSet -> [PermissionName]
validatePermissionActionSet config =
  filter (not . permissionNameOk) . HashSet.toList {- n.b. removes duplicates -} . HashSet.map permissionActionName
  where
    ds = configDeclarations config
    permissionNameOk n = n `Map.member` ds

-- | @validatePermissions config calltree@ returns a list of logger entries for
-- each permission name that appears on explicit declarations in @calltree@
-- that was not declared in @config@
validatePermissions :: Config -> CallMap -> [Entry]
validatePermissions config =
  report
  . Map.filter (not . null . snd)
  . Map.map (\(ni,_callTree,actions) -> (ni, validatePermissionActionSet config actions))
  where
    report :: Map.Map Ident (NodeInfo, [PermissionName]) -> [Entry]
    report = map (\(i, (ni, names)) -> Warning ni (explain i names)) . Map.toList
    explain :: Ident -> [PermissionName] -> Text.Text
    explain i names =
      "The permissions of " <> (Text.pack $ show i)
      <> " [" <> commaSepText names <>  "]"
      <> " were not found in the config file, possible typos?"
    commaSepText :: [PermissionName] -> Text.Text
    commaSepText = Text.intercalate ", " . map (\(PermissionName txt) -> txt)

-- | Given a set of permission actions (either inferred or explicitly annotated)
-- compute the permission presense available on entry to the function.
initialSite :: [PermissionAction] -> Site
initialSite =
  getJoin . foldMap actionPrecondition

-- | Given the permission action of a call, return
-- the permission presence that must be true /prior/ to the call.
--
-- If a call needs, uses or revokes a permission, then it must have that
-- permission prior to the call.  (And if it uses it, it must indicate
-- that too).
-- If a call grants or denies a permission, then it must lack it prior to the call
actionPrecondition :: PermissionAction -> Join Site
actionPrecondition (Need p) = site p has
actionPrecondition (Use p) = site p (uses \/ has)
actionPrecondition (Revoke p) = site p has
actionPrecondition (Deny p) = site p lacks
actionPrecondition (Grant p) = site p lacks
actionPrecondition (Waive _p) = mempty

actionPostcondition :: PermissionAction -> PermissionPresence
actionPostcondition (Grant {}) = has
actionPostcondition (Revoke {}) = lacks
actionPostcondition _ = bottom

-- | Convenience function for building call site info.
site :: PermissionName -> PermissionPresence -> Join Site
site pn = Join . singletonPresence pn

-- | Convenience function to help type inference in message formatting.
strConcat :: [String] -> String
strConcat = concat

