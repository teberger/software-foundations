module LcData where

import Data.Map as M

type VarName = String

data Term = Identifier VarName | 
            Abstraction VarName Term |
            Application Term Term |
            If Term Term Term |
            Fix Term |
            Succ Term |
            Pred Term |
            IsZero Term |
            Tru |
            Fls |
            Zero deriving Eq

data Type = Function Type Type |
            Boole |
            Nat |
            NullType deriving Eq

instance Show Term where
  show (Identifier name) = "Identifier " ++ name
  show (Abstraction name t) = "Abstraction " ++ name ++  " (" ++ (show t) ++ ")"
  show (Application t1 t2) = "Application (" ++ (show t1) ++") ("++ (show t2) ++ ")"
  show (If t1 t2 t3) = "If (" ++ show t1 ++ ") then (" ++ show t2 ++ ") else (" ++ show t3 ++ ") fi"
  show (Fix t) = "Fix (" ++ show t ++ ")"
  show (Succ t) = if isNumeric t
                  then show $ convert (Succ t)
                  else "Succ " ++ show t
  show (Pred t) = "Pred (" ++ show t ++ ")"
  show (IsZero t) = "IsZero (" ++ show t ++ ")"
  show Tru = "True"
  show Fls = "False"
  show Zero = "0"

instance Show Type where
  show Boole = "Boolean"
  show Nat = "Nat"
  show (Function t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
  show NullType = "<NULL>"

type TypeContext = M.Map VarName Type

isNumeric :: Term -> Bool
isNumeric Zero = True
isNumeric (Succ t) = isNumeric t
isNumeric _ = False

isValue :: Term -> Bool
isValue Tru = True
isValue Fls = True
isValue (Identifier _) = True
isValue (Abstraction _ _) = True
isValue t = isNumeric t


convert :: Term -> Int
convert (Succ t) = 1 + convert t
convert Zero = 0
