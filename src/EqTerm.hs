module EqTerm

where

import           Data.List as List
import qualified Data.Map.Strict as Map

import           CNF
import           Equality
import           PropLogic
import           SAT
import           Tseitin
import           Types

type EqTerm = TermT Equality


--- | Erzeugt ein Atom für Gleichheit
(===) :: Symbol -> Symbol -> EqTerm
a === b = BVar (Equal a b)


--- | Erzeugt ein Atom für Ungleichheit
(=/=) :: Symbol -> Symbol -> EqTerm
a =/= b = BVar (NonEq a b)


-- | Diese Funktion prüft eine 'Valuation' vom Typ 'Equality' auf Konsistenz.
--
-- Die 'Equality' Werte werden dazu normalisiert, d.h., z.B. aus `(NonEq t1 t2,
-- False)` wird `(Eq t1 t2)` und alle 'Equality' Werte mit Hilfsvariablen werden
-- entfernt.
--
--
checkConsistency :: Valuation Equality -> Bool
checkConsistency val  = consistent normalizedList
  where normalizedList = map normalizeEqTermBool (cleanEqTerms (Map.toList val))


normalizeEqTermBool :: (Equality, Bool) -> Equality
normalizeEqTermBool eqtb =
  case eqtb of
    (t, True)  -> t
    (t, False) -> negateEqTerm t

negateEqTerm :: Equality -> Equality

negateEqTerm (Equal s1 s2) = NonEq s1 s2
negateEqTerm (NonEq s1 s2) = Equal s1 s2


negEqTermBool :: (Equality, Bool) -> EqTerm
negEqTermBool (eqTerm, b) =
  case (eqTerm, b) of
    (t, True)  -> Neg $ BVar t
    (t, False) -> BVar t


-- | Negiere eine Lösung des Solvers und bilde daraus einen Wert vom Typ
-- 'EqTerm'.
negateSolution :: [(Equality, Bool)] -> EqTerm
negateSolution [] = error "cannot have empty clause here"
negateSolution [p]  = negEqTermBool p
negateSolution (p:rest) = negateSolution rest \/ eqt
  where eqt = negEqTermBool p


-- | Removes auxiliary terms from solution, returns list of 'Equality'
cleanEqTermPairs :: [(Equality, Bool)] -> [Equality]
cleanEqTermPairs eqTerms = map normalizeEqTermBool (cleanEqTerms eqTerms)

-- | Removes auxiliary terms, returns list of '(Equality, Bool)' pairs.
cleanEqTerms :: [(Equality, Bool)] -> [(Equality, Bool)]
cleanEqTerms [] = []
cleanEqTerms (p@(e, _):rest) =
  if isPrefixOf "aux" (case e of
                          Equal (Var t) _ -> t
                          NonEq (Var t) _ -> t
                          _               -> "notAPrefix")
  then cleanEqTerms rest
  else p:cleanEqTerms rest




---------------
-- Aufgabe 3 --
---------------


-- | Die Funktion 'solveT' entscheidet ob der gegebene Wert vom Typ 'EqTerm'
-- erfüllbar ist. Dazu wird mit 'solveCNF' eine Lösung der Strukturformel
-- gesucht.
--
-- Wenn es keine solche Lösung gibt ist das Ergebnis 'Nothing', ansonsten wird
-- das Resultat auf Konsistenz geprüft (mittels 'checkConsistency').
--
-- Wenn die Lösung auch konsistent in UF ist, dann wird diese Lösung
-- zurückgegeben. Ansonsten wird analog des `lazy-basic` Algorithmus weiter
-- gerechnet.
--
-- Aus einer 'Valuation' `val` bekommen Sie mit 'Map.toList val' eine Liste von
-- '(Equality, Bool)'. Mit 'cleanEqTerms' können Sie aus einer Liste von
-- '[(Equality, Bool)]' Werten alle unnötigen Hilfsvariablen entfernen.
solveT :: EqTerm -> Maybe (Valuation Equality)
solveT t =
  let solution = solveCNF t
  in case solution of
       Nothing  -> Nothing
       Just sol -> undefined


solveEqTerm :: EqTerm -> IO ()
solveEqTerm t =
  if isCNF t then do
    let sol = solveT t
    case sol of
      Nothing -> putStrLn ("no solution found for " ++ show t)
      Just s  -> do
        let sol' = map normalizeEqTermBool (Map.toList s)
        putStrLn ("solution: " ++ show (List.nub sol'))
    else
    putStrLn (show t ++ " is not in CNF")


---------------
-- Aufgabe 3 --
---------------

proveLemma :: EqTerm -> IO ()
proveLemma t = undefined


---------------
-- Aufgabe 4 --
---------------

-- | Diese Funktion verstärkt Constraints so dass diese weiterhin inkonsistent
-- bleiben. Nutzt nur 'consistent', keinen SAT-Solver.
strengthenConstraint :: [(Equality, Bool)] -> [(Equality, Bool)]
strengthenConstraint valList = undefined
