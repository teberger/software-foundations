module LcEvaluator where 

import LcData
  
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

eval :: Term -> Term
eval t = case eval1 t of
          Just t1 -> eval t1
          Nothing -> t

eval1 :: Term -> Maybe Term
eval1 t 
  | isValue t = Nothing
  | otherwise = case t of
                 Application t1 t2 -> evalApplication t1 t2
                 If t1 t2 t3 -> evalIf t1 t2 t3
                 IsZero t -> evalIsZero t
                 Succ t -> evalSucc t 
                 Pred t -> evalPred t
                 otherwise -> Nothing

betaReduc :: VarName -> Term -> Term -> Term
betaReduc l r (Identifier name) = if name == l
                                  then r
                                  else (Identifier name)
betaReduc l r (Abstraction name term) = Abstraction name $ betaReduc l r term
betaReduc l r (Application t1 t2) = Application (betaReduc l r t1) (betaReduc l r t2)
betaReduc l r (If t1 t2 t3) = If (betaReduc l r t1) (betaReduc l r t2) (betaReduc l r t3)
betaReduc l r (Succ t) = Succ (betaReduc l r t)
betaReduc l r (Pred t) = Pred (betaReduc l r t)
betaReduc l r (IsZero t) = IsZero (betaReduc l r t)
betaReduc l r t = t

evalApplication :: Term -> Term -> Maybe Term
evalApplication t1@(Abstraction name t) t2
  | isValue t2 = Just (betaReduc name t2 t)
  | otherwise = eval1 t2 >>= return . (Application t1)
evalApplication t1 t2
  | isValue t1 = eval1 t2 >>= return . (Application t1)
  | otherwise = eval1 t1 >>= return . \t -> (Application t t2)

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
