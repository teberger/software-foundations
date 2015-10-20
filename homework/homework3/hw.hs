module Main where

data Term = Tru |
            Fls |
            Zero |
            If Term Term Term |
            Succ Term |
            Pred Term |
            IsZero Term
          deriving Eq

instance Show Term where
  show Tru = "TRUE"
  show Fls = "FALSE"
  show Zero = "ZERO"
  show (If t1 t2 t3) = "IF " ++ show t1 ++
                       " THEN " ++ show t2 ++
                       " ELSE " ++ show t3
  show (Succ t) = "SUCC " ++ show t
  show (Pred t) = "PRED " ++ show t
  show (IsZero t) = "ISZERO " ++ show t
  
isValue :: Term -> Bool
isValue Fls = True
isValue Tru = True
isValue Zero = True
isValue (Succ t) = True
isValue _ = False

isNumericValue :: Term -> Bool
isNumericValue Zero = True
isNumericValue (Succ t) = True
isNumericValue _ = False

eval1 :: Term -> Maybe Term
eval1 Tru = Just Tru
eval1 Fls = Just Fls
eval1 Zero = Just Zero 
eval1 (Succ t) = Just (Succ t)

eval1 (Pred Zero) = Just Zero
eval1 (Pred (Succ t)) = Just t
eval1 (Pred t) = eval1 t >>= (Just . Pred)

                  
eval1 (IsZero Zero) = Just Tru
eval1 (IsZero (Succ t)) = Just Fls
eval1 (IsZero t) = eval1 t >>= Just . IsZero

eval1 (If Tru t2 _) = Just t2
eval1 (If Fls _ t3) = Just t3
eval1 (If t1 t2 t3) = case eval1 t1 of
                       Just Tru -> Just t2
                       Just Fls -> Just t3
                       Just _ -> Nothing
                       Nothing -> Nothing

eval :: Term -> Term
eval t = case eval1 t of
          Just t1 -> if isValue t1
                     then t1
                     else eval t1
          Nothing -> t
