module LcData where

import Data.Map as M 

type VarName = String

data Term = Identifier VarName | 
            Abstraction VarName Term |
            Application Term Term |
            If Term Term Term |
            Succ Term |
            Pred Term |
            IsZero Term |
            Tru |
            Fls |
            Zero deriving (Eq, Show)

data Type = Function Type Type |
            Boole |
            Nat |
            NullType deriving Eq

instance Show Type where
  show Boole = "Boolean"
  show Nat = "Nat"
  show (Function t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show NullType = "<NULL>"

type TypeContext = M.Map VarName Type
