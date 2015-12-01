module Syntax where

import qualified Data.Map as M

type Identifier = String

data Type =
  TypeArrow Type Type |
  TypeVar Identifier |
  TypeNat  |
  TypeBool deriving (Show, Eq)
  
data Term =
  Abs Identifier Type Term |
  App Term Term |
  Var Identifier |
  Fix Term |
  If Term Term Term |
  Succ Term |
  Pred Term |
  IsZero Term |
  Zero |
  Tru |
  Fls deriving Eq

instance Show Term where
  show (Var name) = "Var " ++ name
  show (Abs name t_type t) = "Abs " ++ name ++
                           ": " ++ (show t_type) ++
                           " (" ++ (show t) ++ ")"
  show (App t1 t2) = "App (" ++ (show t1) ++") ("++ (show t2) ++ ")"
  show (If t1 t2 t3) = "If (" ++ show t1 ++
                       ") then (" ++ show t2 ++
                       ") else (" ++ show t3 ++
                       ") fi"
  show (Fix t) = "Fix (" ++ show t ++ ")"
  show (Succ t) = if isNumeric t
                  then show $ convertNumeric (Succ t)
                  else "Succ (" ++ show t ++ ")"
  show (Pred t) = "Pred (" ++ show t ++ ")"
  show (IsZero t) = "IsZero (" ++ show t ++ ")"
  show Tru = "True"
  show Fls = "False"
  show Zero = "0"

{-
| Determines if the value is a numeric value or not
| Zero is always numeric
| Succ v is numeric iff v is numeric
| 
--}
isNumeric :: Term -> Bool
isNumeric Zero = True
isNumeric (Succ t) = isNumeric t
isNumeric _ = False

isValue :: Term -> Bool
isValue Tru = True
isValue Fls = True
isValue (Var _) = True
isValue (Abs _ _ _) = True
isValue t = isNumeric t

convertNumeric :: Term -> Int
convertNumeric (Succ t) = 1 + convertNumeric t
convertNumeric Zero = 0

  
