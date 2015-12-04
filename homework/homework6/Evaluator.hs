module Evaluator where 

import Syntax
import Data.List (delete)
import Control.Monad.State.Lazy

evalType :: Term -> State [(Identifier, Type)] Type
evalType (Abs id id_type t) = do
  types <- get
  let t_type = (id, id_type)
  put (t_type:types)
  r <- evalType t 
  put $ delete t_type types
  return $ (TypeArrow id_type r)
evalType (App t1 t2) = do 
  t1' <- evalType t1
  t2' <- evalType t2
  case t1' of
   (TypeArrow s1 s2) -> case s1 == t2' of
     True -> return t2'
     False -> fail "parameter types do no match"
   otherwise -> fail "t1 not a function type"
evalType (If t1 t2 t3) = do
  t1_type <- evalType t1
  t2_type <- evalType t2
  t3_type <- evalType t3
  case (t2_type == t3_type) && t1_type == TypeBool of
   True -> return t2_type
   False -> fail "t2 /= t3 or t1 not a bool" 
evalType (Var v) = do
  types <- get
  case lookup v types of
   Just a -> return a
   Nothing -> fail ""
evalType (Fix t) = do
  t_type <- evalType t
  case t_type of
   (TypeArrow t1 t2) -> return $ t1
   otherwise -> fail ""
evalType (Succ t) = do
  t_type <- evalType t
  case t_type of
   TypeNat -> return $ TypeNat
   otherwise -> fail ""
evalType (Pred t) = do
  t_type <- evalType t
  case t_type of
   TypeNat -> return $ TypeNat
   otherwise -> fail ""
evalType (IsZero t) = do
  t_type <- evalType t
  case t_type of
   TypeNat -> return $ TypeBool
   otherwise -> fail ""
evalType Zero = return TypeNat
evalType Tru = return TypeBool
evalType Fls = return TypeBool

eval :: Term -> Term
eval t = case eval1 t of
          Just t1 -> eval t1
          Nothing -> t

eval1 :: Term -> Maybe Term
eval1 t 
  | isValue t = Nothing
  | otherwise = case t of
                 Fix t -> evalFix t
                 App t1 t2 -> evalApplication t1 t2
                 If t1 t2 t3 -> evalIf t1 t2 t3
                 IsZero t -> evalIsZero t
                 Succ t -> evalSucc t 
                 Pred t -> evalPred t
                 otherwise -> Nothing

evalFix :: Term -> Maybe Term
evalFix a@(Abs varname _ t) = Just $ betaReduc varname (Fix a) t
evalFix t = eval1 t >>= return . Fix

evalApplication :: Term -> Term -> Maybe Term
evalApplication t1@(Abs name _ t) t2
  | isValue t2 = Just (betaReduc name t2 t)
  | otherwise = eval1 t2 >>= return . (App t1)
evalApplication t1 t2
  | isValue t1 = eval1 t2 >>= return . (App t1)
  | otherwise = eval1 t1 >>= return . \t -> (App t t2)

evalIf :: Term -> Term -> Term -> Maybe Term
evalIf Tru t2 t3 = Just t2
evalIf Fls t2 t3 = Just t3
evalIf t1 t2 t3 = eval1 t1 >>= return . \t -> (If t t2 t3)

evalSucc :: Term -> Maybe Term
evalSucc t = eval1 t >>= Just . Succ

evalPred :: Term -> Maybe Term
evalPred (Succ t) = Just t
evalPred Zero = Just Zero
evalPred t = eval1 t >>= Just . Pred 

evalIsZero :: Term -> Maybe Term
evalIsZero Zero = Just Tru
evalIsZero (Succ t)
  | isNumeric t = Just Fls
  | otherwise = Nothing
evalIsZero t = eval1 t >>= Just . IsZero 
