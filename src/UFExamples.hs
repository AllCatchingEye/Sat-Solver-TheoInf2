module UFExamples

where

import           EqTerm
import           Equality
import           PropLogic

x1 :: Symbol
x1 = Var "x1"
x2 :: Symbol
x2 = Var "x2"
x3 :: Symbol
x3 = Var "x3"
x4 :: Symbol
x4 = Var "x4"

exampleEqTerm0 :: EqTerm
exampleEqTerm0 = ((x1 === x2) \/ (x1 === x3))
              /\ ((x1 === x2) \/ (x1 === x4))
              /\ (x1 =/= x2)
              /\ (x1 =/= x3)
              /\ (x1 =/= x4)

x :: Symbol
x = Var "x"
y :: Symbol
y = Var "y"
z :: Symbol
z = Var "z"

exampleEqTerm1 :: EqTerm
exampleEqTerm1 = (x === y)
              /\ ((y === z) \/ (x === z))
              /\ ((x =/= z) \/ (x === z))


f :: Symbol -> Symbol
f = Fun1 "F"
x5 :: Symbol
x5 = Var "x5"

exampleEqTerm2 :: EqTerm
exampleEqTerm2 = (x1 === x2) /\ (x2 === x3) /\ (x4 === x5) /\ (x5 =/= x1)
              /\ (f x1 =/= f x3)


exampleEqTerm3 :: EqTerm
exampleEqTerm3 = (x1 === f x2) /\ (f x1 =/= f (f x2))

-- | UF example from "decision procedures" 4.2.2

-- binary uninterpreted function for multiplication
m :: Symbol -> Symbol -> Symbol
m      = Fun2 "Mult"

-- for program A
out0_a :: Symbol
out0_a = Var "out0_a"
out1_a :: Symbol
out1_a = Var "out1_a"
out2_a :: Symbol
out2_a = Var "out2_a"
in0_a :: Symbol
in0_a  = Var "in0_a"
progA :: EqTerm
progA = (out0_a === in0_a)
     /\ (out1_a === m out0_a in0_a)
     /\ (out2_a === m out1_a in0_a)

-- for program B
out0_b :: Symbol
out0_b = Var "out0_b"
in0_b :: Symbol
in0_b  = Var "in0_b"
progB :: EqTerm
progB  = out0_b === m (m in0_b in0_b) in0_b

-- program equivalency: on equal inputs the programs imply equal outputs
-- we want to prove

verify :: EqTerm
verify = ((in0_a === in0_b) /\ progA /\ progB) --> (out2_a === out0_b)


--- example Lemmas

a :: Symbol
a = Var "a"
b :: Symbol
b = Var "b"
e :: Symbol
e = Var "e"


eqLemma1 :: EqTerm
eqLemma1 = ((a === b) /\ (b === e)) --> (a === e)

eqLemma2 :: EqTerm
eqLemma2 = ((a =/= b) /\ (b === e)) --> (a =/= e)

eqLemma3 :: EqTerm
eqLemma3 = ((a =/= b) /\ (b === e)) --> (a === e)

eqLemma4 :: EqTerm
eqLemma4 = (a =/= b) --> (f a =/= f b)

funcLemma1 :: EqTerm
funcLemma1 = (x === y) --> (m x y === m x x)

funcLemma2 :: EqTerm
funcLemma2 = (x === f y) --> (m x y === m x x)

funcLemma3 :: EqTerm
funcLemma3 = (x === f y) --> (m (f y) x === m x y)

funcLemma4 :: EqTerm
funcLemma4 = (x === f y) --> (m (f y) x === m x x)


-- example from "decision procedures"  4.5.1 "Proving Equivalence of Circuits"
k :: Symbol -> Symbol
k = Fun1 "K"
g :: Symbol -> Symbol
g = Fun1 "G"
h :: Symbol -> Symbol
h = Fun1 "H"
c :: Symbol -> Symbol
c = Fun1 "C"
d :: Symbol -> Symbol
d = Fun1 "D"

wahr :: Symbol
wahr   = Var "w"
falsch :: Symbol
falsch = Var "f"

input :: Symbol
input = Var "in"
l1 :: Symbol
l1    = Var "L1"
l2 :: Symbol
l2    = Var "L2"
l3 :: Symbol
l3    = Var "L3"
l4 :: Symbol
l4    = Var "L4"
l5 :: Symbol
l5    = Var "L5"

predicate :: Symbol -> EqTerm
predicate t = (t === wahr) \/ (t === falsch)

theory451 :: EqTerm
theory451 = wahr =/= falsch
         /\ predicate (c l2)
         /\ predicate (c l1')
         /\ predicate l2'

circuit1 :: EqTerm
circuit1 = (l1 === f input)
        /\ (l2 === l1)
        /\ (l3 === k (g l1))
        /\ (l4 === h l1)
        /\ ((c l2 === wahr --> (l5 === l3)) /\ (c l2 === falsch --> (l5 === d l4)))

l1' :: Symbol
l1' = Var "L1'"
l2' :: Symbol
l2' = Var "L2'"
l3' :: Symbol
l3' = Var "L3'"
l4' :: Symbol
l4' = Var "L4'"
l5' :: Symbol
l5' = Var "L5'"

circuit2 :: EqTerm
circuit2 = (l1' === f input)
        /\ (l2' === c l1')
        /\ ((c l1' === wahr --> (l3' === g l1')) /\ (c l1' === falsch --> (l3' === h l1')))
        /\ ((l2' === wahr --> (l5' === k l3')) /\ (l2' === falsch --> (l5' === d l3')))

circuitsEqual :: EqTerm
circuitsEqual = (theory451 /\ circuit1 /\ circuit2) --> (l5 === l5')


--------------------------------------------------------------------
-- 4.5.2 Verifying a Compilation Process with Translation Validation
--------------------------------------------------------------------


u1 :: Symbol
u1 = Var "u1"

u2 :: Symbol
u2 = Var "u2"

y1 :: Symbol
y1 = Var "y1"

y2 :: Symbol
y2 = Var "y2"

compilationLemma :: EqTerm
compilationLemma =
  ((u1 === (f x1 y1)) /\ (u2 === (f x2 y2)) /\ (z === (g u1 u2)))
     --> (z === (g (f x1 y1) (f x2 y2)))
