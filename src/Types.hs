module Types

where

import           Data.Map.Strict ()
import           Data.Map.Strict as Map


data TermT a = Top
             | Bottom
             | Neg (TermT a)
             | BVar a
             | Conj (TermT a) (TermT a)
             | Disj (TermT a) (TermT a)
             | Equiv (TermT a) (TermT a)
             | Impl (TermT a) (TermT a)
             deriving (Eq, Ord)

type Term = TermT String

instance Show a => Show (TermT a) where
  show Bottom = " F "
  show Top = " T "
  show (BVar a) = "'" ++ show a ++ "'"
  show (Neg t) = "~ " ++ show t
  show (Conj t1 t2) = "(" ++ show t1 ++ " /\\ " ++ show t2 ++ ")"
  show (Disj t1 t2) = "(" ++ show t1 ++ " \\/ " ++ show t2 ++ ")"
  show (Impl t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show (Equiv t1 t2) = "(" ++ show t1 ++ " <-> " ++ show t2 ++ ")"

data TTermT a = TTop    Int
              | TBottom Int
              | TNeg    Int (TTermT a)
              | TBVar   Int a
              | TConj   Int (TTermT a) (TTermT a)
              | TDisj   Int (TTermT a) (TTermT a)
              | TEquiv  Int (TTermT a) (TTermT a)
              | TImpl   Int (TTermT a) (TTermT a)
             deriving (Eq, Ord)

type TTerm = TTermT String

type Valuation a = Map a Bool
type Values a = [(a, Bool)]

getVal :: Ord a => Valuation a -> a -> Maybe Bool
getVal values varName = Map.lookup varName values

readValues :: Ord a => [(a, Bool)] -> Valuation a
readValues = Map.fromList


termSize :: TermT a -> Int

termSize Top      = 1
termSize Bottom   = 1
termSize (BVar _) = 1

termSize (Neg t) = 1 + termSize t

termSize (Conj t1 t2)  = 1 + termSize t1 + termSize t2
termSize (Disj t1 t2)  = 1 + termSize t1 + termSize t2
termSize (Impl t1 t2)  = 1 + termSize t1 + termSize t2
termSize (Equiv t1 t2) = 1 + termSize t1 + termSize t2
