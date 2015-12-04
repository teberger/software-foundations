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
  Let Identifier Term Term |
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
  show (Let id t1 t2) = "Let " ++ id ++ " = " ++ show t1 ++
                        " in " ++ show t2
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
  
betaReduc :: Identifier -> Term -> Term -> Term
betaReduc l r (Var name) = if name == l
                           then r
                           else (Var name)
-- any var with this name is bound to a different abstraction and
-- should not be replaced via the current beta reduction
betaReduc l r (Abs id id_type term) = if id == l
                                      then Abs id id_type term
                                      else Abs id id_type (betaReduc l r term)
betaReduc l r (Let id t1 t2) = if id == l
                               then Let id t1 t2
                               else Let id (betaReduc l r t1)
                                           (betaReduc l r t2)
betaReduc l r (App t1 t2) = App (betaReduc l r t1)
                                (betaReduc l r t2)
betaReduc l r (If t1 t2 t3) = If (betaReduc l r t1)
                                 (betaReduc l r t2)
                                 (betaReduc l r t3)
betaReduc l r (Succ t) = Succ (betaReduc l r t)
betaReduc l r (Pred t) = Pred (betaReduc l r t)
betaReduc l r (IsZero t) = IsZero (betaReduc l r t)
betaReduc l r t = t

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
isValue (IAbs _ _) = True
isValue t = isNumeric t

convertNumeric :: Term -> Int
convertNumeric (Succ t) = 1 + convertNumeric t
convertNumeric Zero = 0

  
