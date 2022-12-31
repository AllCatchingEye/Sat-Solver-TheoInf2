module CNF

where

import           NormalForm
import           Types

cnf' :: Eq a => TermT a -> TermT a
cnf' t = let t' = cnf t in if isCNF t' then t' else
                             if t == t' then error "blub" else cnf' t'

cnf :: Eq a => TermT a -> TermT a

cnf Bottom = Bottom
cnf Top = Top
cnf t@(BVar _) = t
cnf (Neg (BVar v)) = Neg (BVar v)

cnf (Disj t1 (Conj t2 t3)) = Conj (Disj t1 t2) (Disj t1 t3)

cnf (Disj (Conj t1 t2) t3) = Conj (Disj t1 t3) (Disj t2 t3)

cnf (Disj t1 t2) = Disj (cnf t1) (cnf t2)
cnf (Conj t1 t2) = Conj (cnf t1) (cnf t2)

cnf _ = error "not in NNF"


isCNF :: TermT a -> Bool
isCNF t = let res = isNNF t && isCNF' t in
            res

isCNF' :: TermT a -> Bool

isCNF' Top     = True
isCNF' Bottom  = True
isCNF' (BVar _) = True
isCNF' (Neg (BVar _)) = True
isCNF' (Neg Top) = True
isCNF' (Neg Bottom) = True

isCNF' (Conj t1 t2) = isCNF' t1 && isCNF' t2
isCNF' (Disj t1 t2) = noConj t1 && noConj t2

isCNF' _ = False



noConj :: TermT a -> Bool

noConj Top      = True
noConj Bottom   = True
noConj (BVar _) = True
noConj (Neg (BVar _)) = True
noConj (Neg Top) = True
noConj (Neg Bottom) = True

noConj (Disj t1 t2) = noConj t1 && noConj t2

noConj _ = False
