module Main where

import           EqTerm
import           UFExamples

main :: IO ()
main = do
  proveLemma circuitsEqual
