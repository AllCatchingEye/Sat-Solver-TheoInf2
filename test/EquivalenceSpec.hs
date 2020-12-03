module EquivalenceSpec
  ( spec )
where

import           Equality

import           Test.Hspec (Spec, describe, it)
import           Test.QuickCheck (Arbitrary, Gen, classify, property, (==>))
import qualified Test.QuickCheck as QC (arbitrary, choose, elements,
                     infiniteList, listOf, shrink, sized, withMaxSuccess)

import           Data.Set (elemAt, union)

varNames :: [String]
varNames = ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "l", "m", "n"]

instance Arbitrary Symbol where
  arbitrary = Var <$> QC.elements varNames

simpleEqClass :: Symbol -> Symbol -> Equivalence
simpleEqClass s1 s2 =
  let c1 = mkEqClass s1
      c2 = mkEqClass s2 in
  Equivalence (union c1 c2)

spec :: Spec
spec = describe "simple equivalence classes" $ do
  it "equal elements are equivalent and unequal elements are non-equivalent" $
    property $ \s1 s2 -> QC.withMaxSuccess 1000 $ do
    let eq = simpleEqClass s1 s2 in
      classify (s1 == s2) "equal" (   (s1 == s2 || not (equivalent eq s1 s2))
                                   && (s1 /= s2 || equivalent eq s1 s2))

  it "merged classes have same symbols" $
    property $ \s1 s2 -> QC.withMaxSuccess 1000 $ do
    let eq0 = simpleEqClass s1 s2
        eq1 = merge eq0 c1 c2
        c1  = elemAt 0 $ mkEqClass s1
        c2  = elemAt 0 $ mkEqClass s2
      in equivalent eq1 s1 s2
