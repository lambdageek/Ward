{-# language OverloadedStrings, StandaloneDeriving, GeneralizedNewtypeDeriving #-}
module Properties where

import Algebra.Algebra
import Types
import Check.Permissions (strongUpdateCap, transferNewNonConflicting)

import qualified Data.Text as Text
import Test.QuickCheck.Instances ()
import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen as Gen

----------------------------------------------------------------------
-- Lattice Properties
----------------------------------------------------------------------

prop_join_commutes :: (Eq a, Show a, JoinSemiLattice a) => a -> a -> QC.Property
prop_join_commutes = prop_fn_commutes (\/)

prop_meet_commutes :: (Eq a, Show a, MeetSemiLattice a) => a -> a -> QC.Property
prop_meet_commutes = prop_fn_commutes (/\)

prop_join_assoc :: (Eq a, Show a, JoinSemiLattice a) => a -> a -> a -> QC.Property
prop_join_assoc = prop_fn_assoc (\/)

prop_meet_assoc :: (Eq a, Show a, MeetSemiLattice a) => a -> a -> a -> QC.Property
prop_meet_assoc = prop_fn_assoc (/\)

prop_join_bottom :: (Eq a, Show a, BoundedJoinSemiLattice a) => a -> QC.Property
prop_join_bottom x = x \/ bottom QC.=== x

prop_join_monotonic :: (Show a, PartialOrd a, JoinSemiLattice a, QC.Arbitrary a) => a -> QC.Property
prop_join_monotonic x = prop_fn_monotonic (\/ x)

prop_meet_monotonic :: (Show a, PartialOrd a, JoinSemiLattice a, MeetSemiLattice a, QC.Arbitrary a) => a -> QC.Property
prop_meet_monotonic x = prop_fn_monotonic (/\ x)

prop_meet_annihilate :: (Eq a, Show a, BoundedJoinSemiLattice a, MeetSemiLattice a) => a -> QC.Property
prop_meet_annihilate x = x /\ bottom QC.=== bottom

prop_join_meet_distrib :: (Eq a, Show a, JoinSemiLattice a, MeetSemiLattice a) => a -> a -> a -> QC.Property
prop_join_meet_distrib = prop_f_g_distrib (\/) (/\)

prop_meet_join_distrib :: (Eq a, Show a, JoinSemiLattice a, MeetSemiLattice a) => a -> a -> a -> QC.Property
prop_meet_join_distrib = prop_f_g_distrib (/\) (\/)

----------------------------------------------------------------------
-- Transfer function properties
----------------------------------------------------------------------

strongUpdateCap_monotonic :: PermissionAction -> QC.Property
strongUpdateCap_monotonic pa = prop_fn_monotonic (strongUpdateCap pa)
  
transferNewNonConflicting_monotonic :: {-PermissionPresenceSet -> -} QC.Property
transferNewNonConflicting_monotonic -- x = prop_fn_monotonic (transferNewNonConflicting x)
  =
  let
    f = transferNewNonConflicting
  in
    QC.forAll QC.arbitrary $ \before1 ->
    QC.forAll (genAboveEq before1) $ \after ->
    QC.forAll (genAboveEq before1) $ \before2 ->
    let
      fa = f after before1
      fb = f after before2
    in
      QC.counterexample (">> after is " ++ show after ++ "\n>> before1 is " ++ show before1 ++ "\n>> before2 is " ++ show before2 ++ "\n>> f before1 is " ++ show fa ++ "\n>> f before2 is " ++ show fb ++ "\n") $
      f after before1 `leq` f after before2

----------------------------------------------------------------------
-- Property combinators
----------------------------------------------------------------------

prop_fn_commutes :: (Eq b, Show b) => (a -> a -> b) -> a -> a -> QC.Property
prop_fn_commutes f = \x y -> f x y QC.=== f y x

prop_fn_assoc :: (Eq a, Show a) => (a -> a -> a) -> a -> a -> a -> QC.Property
prop_fn_assoc f = \x y z -> x `f` (y `f` z) QC.=== (x `f` y) `f` z


-- | Given two functions @f@ ang @g@ check that @g@ distributes over @f@, that
-- is: @(x `f` y) `g` z = (x `g` z) `f` (y `g` z)@
prop_f_g_distrib :: (Eq a, Show a) => (a -> a -> a) -> (a -> a -> a) -> a -> a -> a -> QC.Property
prop_f_g_distrib f g = \x y z -> (x `f` y) `g` z QC.=== (x `g` z) `f` (y `g` z)

-- | Check that the given function is monotonic by feeding it @x@ and @x \\\/
-- y@ where @x@ and @y@ are arbitrary elements of the lattice.
-- 
prop_fn_monotonic :: (Show a, PartialOrd a, JoinSemiLattice a, QC.Arbitrary a) => (a -> a) -> QC.Property
prop_fn_monotonic f =
  QC.forAll QC.arbitrary $ \a ->
  QC.forAll (genAboveEq a) $ \b ->
  QC.cover (a /= b) 90 "non-trivial" $
  f a `leq` f b


----------------------------------------------------------------------
-- Orphan Arbitrary instances
----------------------------------------------------------------------

instance QC.Arbitrary Usage where
  arbitrary = Gen.elements [UsageUnknown, Uses]

instance QC.Arbitrary Capability where
  arbitrary = Gen.elements [CapUnknown, CapHas, CapLacks, CapConflict]

instance QC.Arbitrary PermissionPresence where
  arbitrary = PermissionPresence <$> QC.arbitrary <*> QC.arbitrary

instance QC.Arbitrary PermissionName where
  arbitrary = Gen.elements $ fmap (PermissionName . Text.singleton) ['a' .. 'h']

deriving instance QC.Arbitrary PermissionPresenceSet

instance QC.Arbitrary PermissionAction where
  arbitrary = Gen.elements fns <*> QC.arbitrary
    where
      fns = [Need, Use, Grant, Revoke, Deny, Waive]

----------------------------------------------------------------------
-- Custom generators
----------------------------------------------------------------------

-- | Given @x@ generate @y@ such that @x `leq` y@.
-- We do this by generating an arbitrary element `z` and returning @x \\\/ z@.
--
-- TODO: check that this gives reasonable examples.
genAboveEq :: (PartialOrd a, JoinSemiLattice a, QC.Arbitrary a) => a -> Gen.Gen a
genAboveEq x = fmap (x \/) QC.arbitrary 
