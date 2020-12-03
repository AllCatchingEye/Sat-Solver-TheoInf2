module PropLogic

where

import           Types (Term (..), TermT (..), Valuation, Values, getVal,
                     readValues)

(<->) :: TermT a -> TermT a -> TermT a
t1 <-> t2 = Equiv t1 t2

(-->) :: TermT a -> TermT a -> TermT a
t1 --> t2 = Impl t1 t2

(\/) :: TermT a -> TermT a -> TermT a
t1 \/ t2 = Disj t1 t2

(/\) :: TermT a -> TermT a -> TermT a
t1 /\ t2 = Conj t1 t2

(¬) :: TermT a -> TermT a
(¬) = negation

(∨) :: TermT a -> TermT a -> TermT a
(∨) = (\/)

negation :: TermT a -> TermT a
negation = Neg

ex1 :: Values String
ex1 = [ ("die Sonne scheint", True)
      , ("es regnet", False)]

ex1Valuation :: Valuation String
ex1Valuation = readValues ex1


evalTerm :: Valuation String -> Term -> Maybe Bool

evalTerm _ Top = Just True
evalTerm _ Bottom = Just False

evalTerm v (Neg t) = case evalTerm v t of
                       Nothing -> Nothing
                       Just v' -> Just (not v')

evalTerm v (BVar varName) = getVal v varName

evalTerm v (Conj t1 t2) =
  case (evalTerm v t1, evalTerm v t2) of
    (Just v1, Just v2) -> Just (v1 && v2)
    _                  -> Nothing

evalTerm v (Disj t1 t2) =
  case (evalTerm v t1, evalTerm v t2) of
    (Just v1, Just v2) -> Just (v1 || v2)
    _                  -> Nothing

evalTerm v (Equiv t1 t2) =
  case (evalTerm v t1, evalTerm v t2) of
    (Just v1, Just v2) -> Just (v1 == v2)
    _                  -> Nothing

evalTerm v (Impl t1 t2) =
  case (evalTerm v t1, evalTerm v t2) of
    (Just v1, Just v2) -> Just (not v1 || v2)
    _                  -> Nothing
