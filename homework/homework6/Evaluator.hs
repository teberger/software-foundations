module Evaluator where 

import Syntax

evalType :: Term -> Type
evalType = undefined

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
