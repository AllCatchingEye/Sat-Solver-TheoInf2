{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Tseitin

where

import           CNF
import           Equality
import           PropLogic
import           Types

-- | Typeclass for the creation of auxiliary variables. This is used for
-- Tseitin's transformation.
--
-- Must create a unique atom given a unique `Int` parameter
class AuxVar a where
  mkAuxVar :: Int -> a

tseitin :: AuxVar a => TermT a -> TermT a
tseitin t = if isCNF t then t else tseitinCNF tt /\ topVar tt
  where (tt, _) = tterm 0 t

tterm :: Int -> TermT a -> (TTermT a, Int)

tterm n Top    = (TTop n, n + 1)
tterm n Bottom = (TBottom n, n + 1)
tterm n (BVar s) = (TBVar n s, n + 1)

tterm n (Conj t1 t2) = (TConj n2 tt1 tt2, n2 + 1)
  where (tt1, n1) = tterm n t1
        (tt2, n2) = tterm n1 t2

tterm n (Disj t1 t2) = (TDisj n2 tt1 tt2, n2 + 1)
  where (tt1, n1) = tterm n t1
        (tt2, n2) = tterm n1 t2

tterm n (Neg t) = (TNeg n1 tt, n1 + 1)
  where (tt, n1) = tterm n t

tterm n (Impl t1 t2) = (TImpl n2 tt1 tt2, n2 + 1)
  where (tt1, n1) = tterm n t1
        (tt2, n2) = tterm n1 t2

tterm n (Equiv t1 t2) = (TEquiv n2 tt1 tt2, n2 + 1)
  where (tt1, n1) = tterm n t1
        (tt2, n2) = tterm n1 t2


instance AuxVar Equality where
  mkAuxVar = eqMkAuxVar

instance AuxVar String where
  mkAuxVar i = "aux" ++ show i

eqMkAuxVar :: Int -> Equality
eqMkAuxVar i =
  Equal (Var ("aux" ++ show (2 * i))) (Var ("aux" ++ show (2 * i + 1)))


topVar :: AuxVar a => TTermT a -> TermT a
topVar (TTop i)       = Top    -- BVar (mkAuxVar i)
topVar (TBottom i)    = Bottom -- BVar (mkAuxVar i)
topVar (TBVar i n)    = BVar n -- (mkAuxVar i)
topVar (TNeg i _)     = BVar (mkAuxVar i)
topVar (TConj i _ _)  = BVar (mkAuxVar i)
topVar (TDisj i _ _)  = BVar (mkAuxVar i)
topVar (TImpl i _ _)  = BVar (mkAuxVar i)
topVar (TEquiv i _ _) = BVar (mkAuxVar i)


tseitinCNF :: AuxVar a => TTermT a -> TermT a

tseitinCNF t@(TTop _)    =
  (negation (topVar t) \/  Top) /\ (negation Top \/ topVar t)

tseitinCNF t@(TBottom _) =
  (negation (topVar t) \/  Bottom) /\ (negation Bottom \/ topVar t)

tseitinCNF t@(TBVar _ v) =
  (negation (topVar t) \/  BVar v) /\ (negation (BVar v) \/ topVar t)

tseitinCNF t@(TNeg _ tt) =
  tseitinCNF tt
  /\
  ((negation (topVar t) \/ negation (topVar tt))
   /\
   (topVar t \/ topVar tt))

tseitinCNF t@(TConj _ t1 t2) =
  let a = topVar t
      x1 = topVar t1
      x2 = topVar t2 in
  tseitinCNF t1
  /\
  (tseitinCNF t2
     /\
     ((negation a \/ x1)
      /\
      ((negation a \/ x2)
       /\
        (a \/ negation x1 \/ negation x2))))

tseitinCNF t@(TDisj _ t1 t2) =
  let a = topVar t
      x1 = topVar t1
      x2 = topVar t2 in
  tseitinCNF t1
  /\
  (tseitinCNF t2
   /\
   ((negation a \/ x1 \/ x2)
    /\
    ((a \/ negation x1)
     /\
     (a \/ negation x2))))

tseitinCNF t@(TImpl _ t1 t2) =  -- wegen neuer Nummerierung hier nicht einfach
                                -- neue Disjunktion mit Negation einführen
  let a = topVar t
      x1 = topVar t1
      x2 = topVar t2 in
  tseitinCNF t1
  /\
  (tseitinCNF t2
   /\
    ((negation a \/ negation x1 \/ x2)
     /\
      ((a \/ x1)
       /\
       (a \/ negation x2))))

tseitinCNF t@(TEquiv _ t1 t2) =
  let a = topVar t
      x1 = topVar t1
      x2 = topVar t2 in
  tseitinCNF t1
  /\
  (tseitinCNF t2
   /\
   ((negation a \/ negation x1 \/ x2)
    /\
    ((negation a \/ x1 \/ negation x2)
    /\
     ((a \/ negation x1 \/ negation x2)
      /\
       (a \/ x1 \/ x2)))))

mkPathologicalExample :: Int -> Term
mkPathologicalExample n =
  if n <= 0 then error "must be positive" else
    foldl1 (\/) l
  where l = map (\i -> BVar ("x" ++ show i) /\ BVar ("y" ++ show i)) [0..n]
