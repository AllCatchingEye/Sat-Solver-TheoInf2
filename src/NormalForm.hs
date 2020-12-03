module NormalForm

where

import           PropLogic
import           Types

nnf :: TermT a -> TermT a

nnf (Neg (Neg a)) = nnf a
nnf (Neg (Conj a b)) = (nnf (Neg a)) \/ (nnf (Neg b))
nnf (Neg (Disj a b)) = (nnf (Neg a)) /\ (nnf (Neg b))
nnf (Neg (Impl a b)) = (nnf a) /\ (nnf (Neg b))
nnf (Neg (Equiv a b)) = ((nnf (Neg a)) /\ (nnf b)) \/ ((nnf a) /\ (nnf (Neg b)))

nnf (Conj a b) = (nnf a) /\ (nnf b)
nnf (Disj a b) = (nnf a) \/ (nnf b)
nnf (Equiv a b) = Conj (nnf (Impl a b)) (nnf (Impl b a))
nnf (Impl a b) = Disj (nnf (Neg a)) (nnf b)

nnf (Neg Bottom) = Top
nnf (Neg Top) = Bottom

nnf v = v


isNNF :: TermT a -> Bool

isNNF (Neg (BVar _)) = True
isNNF (Neg Top) = True
isNNF (Neg Bottom) = True
isNNF (Neg _) = False

isNNF (Conj t1 t2) = isNNF t1 && isNNF t2

isNNF (Disj t1 t2) = isNNF t1 && isNNF t2

isNNF (BVar _) = True

isNNF Top = True
isNNF Bottom = True

isNNF _ = False
