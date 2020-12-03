module EqualitySpec
  (spec)
where

import           EqTerm
import           Equality

import           Test.Hspec (Spec, describe, it, shouldBe)
import           Test.QuickCheck (Arbitrary, Gen, classify, property, (==>))
import qualified Test.QuickCheck as QC (arbitrary, choose, elements,
                     infiniteList, listOf, shrink, sized, withMaxSuccess)

import           Data.Set (elemAt, toList, union)

import           Debug.Trace as D

x :: Symbol
x = Var "x"

y :: Symbol
y = Var "y"

f :: Symbol -> Symbol -> Symbol
f = Fun2 "f"

g :: Symbol -> Symbol
g = Fun1 "G"

spec :: Spec
spec = describe "compareEquality" $ do
  it "equal Symbols are equal" $ do
    (x === y) == (y === x) `shouldBe` True
    (g x === y)  == (y  === g x) `shouldBe` True
    (f x y === g x) == (g x === f x y) `shouldBe` True

  it "not equal Symbol comparisons are equal" $ do
    (x =/= y) == (y =/= x) `shouldBe` True
    (g x =/= y)  == (y  =/= g x) `shouldBe` True
    (f x y =/= g x) == (g x =/= f x y) `shouldBe` True

  it "different comparisons are not equal" $ do
    (x === y) == (g x === g y) `shouldBe` False
    (x === y) == (f x (g y) =/= g (f y (g x))) `shouldBe` False


  describe "congruence closure for functions" $ do
    let c1 = mkEqClass x
        c2 = mkEqClass y
        c3 = mkEqClass (g x)
        c4 = mkEqClass (g y)
        c5 = mkEqClass (f x x)
        c6 = mkEqClass (f y y)
        eqv0 = mkEquivalence $ toList (c1 `union` c2 `union` c3 `union` c4)
        eqv1 = merge eqv0 (getClass eqv0 x) (getClass eqv0 y)
        eqv2 = mkEquivalence $ toList (c1 `union` c2 `union` c5 `union` c6)
        eqv3 = merge eqv2 (getClass eqv0 x) (getClass eqv0 y)
    it "with one parameter" $ do
      D.trace (show c3) $
       equivalent (congruenceClosure eqv1) (g x) (g y)

    it "with two parameters" $ do
      equivalent (congruenceClosure eqv3) (f x x) (f y y)
