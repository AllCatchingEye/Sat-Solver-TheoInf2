module SAT

where

import           CNF
import           PropLogic
import           Tseitin
import           Types

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import           CDCL.Algorithm as CDCL
import           CDCL.Types

data IndexedVars a = IndexedVars
  { intToVarName :: Map Int a
  , varNameToInt ::  Map a Int
  } deriving (Show)



-- | Diese Funktion gibt den Index des Literals mit dem Namen 'n' in der BiMap
-- 'idx' zurück. Wenn der Name nicht vorhanden ist, gibt es die von `Map.!`
-- ausgelöste Exception.
getIndexOf :: Ord a => IndexedVars a -> a -> Int
getIndexOf (IndexedVars _ vMap) n = vMap Map.! n

getNameOf :: IndexedVars a -> Int -> a
getNameOf (IndexedVars iMap _) i = iMap Map.! i


example1 :: Term
example1 = BVar "x" --> (BVar "a" /\ BVar "b")

example2 :: Term
example2 = Neg (BVar "x")

example3 :: Term
example3 = example1 \/ example2

example4 :: Term
example4 = example3 /\ negation example3

indexVars :: Ord a => TermT a -> IndexedVars a
indexVars = flip indexVariables (IndexedVars Map.empty Map.empty)

indexVariables :: Ord a => TermT a -> IndexedVars a -> IndexedVars a

indexVariables Top vars    = vars
indexVariables Bottom vars = vars
indexVariables (BVar name) vars =
  if Map.member name (varNameToInt vars)
  then vars
  else
    IndexedVars { intToVarName = Map.insert nextIndex name (intToVarName vars)
                , varNameToInt = Map.insert name nextIndex (varNameToInt vars) }
  where nextIndex = 1 + Map.size (intToVarName vars)

indexVariables (Neg t) vars = indexVariables t vars

indexVariables (Conj t1 t2) vars = indexVariables t2 vars'
  where vars' = indexVariables t1 vars

indexVariables (Disj t1 t2) vars = indexVariables t2 vars'
  where vars' = indexVariables t1 vars

indexVariables (Impl t1 t2) vars = indexVariables t2 vars'
  where vars' = indexVariables t1 vars

indexVariables (Equiv t1 t2) vars = indexVariables t2 vars'
  where vars' = indexVariables t1 vars



convertClauses :: Ord a => IndexedVars a -> TermT a -> [[Int]]

convertClauses idxVars (Conj c1 c2) =
  convertClauses idxVars c1 ++ convertClauses idxVars c2

convertClauses idxVars c@(Disj _ _) = [convertClause idxVars c]
convertClauses idxVars c@(Neg (BVar _)) = [convertClause idxVars c]
convertClauses idxVars c@(BVar _) = [convertClause idxVars c]

convertClauses _ _ = error "not in CNF"



convertClause :: Ord a => IndexedVars a -> TermT a -> [Int]

convertClause idxVars@(IndexedVars _ v2i) (Disj c c2) =
  convertClause idxVars c ++ convertClause idxVars c2

convertClause (IndexedVars _ v2i) (Neg (BVar n)) = [-(v2i Map.! n)]
convertClause (IndexedVars _ v2i) (BVar n)       = [v2i Map.! n]

convertClause _ _ = error "only var or negated var is allowed"


solveCNF :: (Ord a, Show a) => TermT a -> Maybe (Valuation a)
solveCNF t =
  if isCNF t
  then
    let indexed  = indexVars t
        solution = CDCL.solve $ convertClauses indexed t
    in case solution of
         Unsatisfiable   -> Nothing
         Satisfiable sol -> Just $ Map.fromList (getSolution indexed sol)

  else Nothing


getSolution :: IndexedVars a -> [Int] -> [(a, Bool)]
getSolution _ [] = []
getSolution idxVars@(IndexedVars i2v _) (v:rest) =
  (name, val) : getSolution idxVars rest
  where name = i2v Map.! abs v
        val = v >= 0
