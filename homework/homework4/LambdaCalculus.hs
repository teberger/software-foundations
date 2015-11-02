module LambdaCalculus where

import Text.Parsec
import Text.Parsec.Char
import Text.ParserCombinators.Parsec.Char

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
            Zero 

data Type = Function Type Type |
            Boole |
            Nat deriving Eq

instance Show Type where
  show Boole = "Boolean"
  show Nat = "Nat"
  show (Function t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"

data TypeContext 

whitespace = many (spaces <|> (many tab >> return ())) >> return ()

keyword p = try $ do
  whitespace
  p' <- string p <?> ("Expecting keyword: " ++ p)
  whitespace

tru :: ParsecT String Type IO Term
tru = try $ do
  keyword "tru"
  setState Boole
  return Tru

fls :: ParsecT String Type IO Term
fls = try $ do
  keyword "fls"
  setState Boole
  return Fls
      
zero :: ParsecT String Type IO Term
zero = try $ do
  keyword "0"
  setState Boole
  return Zero

iszero :: ParsecT String Type IO Term
iszero = try $ do
  keyword "iszero"
  keyword "("
  t <- term <?> "Error parsing: Succ ( Term )"
  t_type <- getState
  if t_type == Nat
  then do
    keyword ")"
    -- change the state from Nat to Boole
    setState Boole
    return (IsZero t)
  else 
    fail $ "Expected type 'Nat' but was " ++ show t_type

succ :: ParsecT String Type IO Term
succ = try $ do
  keyword "succ"
  keyword "("
  t <- term <?> "Error parsing: Succ ( Term )"
  t_type <- getState
  if t_type == Nat
  then do
    -- no need to change the state, it is the same
    keyword ")"
    return (Succ t)
  else 
    fail $ "Expected type 'Nat' but was " ++ show t_type

pred :: ParsecT String Type IO Term 
pred = try $ do
  keyword "pred"
  keyword "("
  t <- term <?> "Error parsing: Pred ( Term )"
  t_type <- getState
  if t_type == Nat
  then do
    -- no need to change the state, it is the same
    keyword ")"
    return (Pred t)
  else 
    fail $ "Expected type 'Nat' but was " ++ show t_type

if_statement :: ParsecT String Type IO Term
if_statement = try $ do
  keyword "if"
  cond <- term <?> "Expecting 'term' following _if_"
  cond_type <- getState
  if cond_type /= Boole
  then
    fail $ "Expecting Boolean type for if-statement conditional, received: " ++
           show cond_type
  else do
    keyword "then"
    t_then <- term <?> "Expecting 'term' following _then_"
    then_type <- getState

    keyword "else"
    t_else <- term <?> "Expecting 'term' following _else_"
    else_type <- getState
    keyword "fi"

    if then_type == else_type
    then do
      setState then_type
      return (If cond t_then t_else)
    else 
      fail $ "Type inconsistency for then/else parts of if statement\n" ++
             "then type: " ++ (show then_type) ++ "\n" ++
             "else type: " ++ (show else_type) ++ "\n"


application :: ParsecT String Type IO Term
application = try $ do
  keyword "app"
  keyword "("
  t1 <- term <?> "Error parsing first 'term' following _app_"
  t1_type <- getState
  keyword ","
  t2 <- term <?> "Error parsing second 'term' following \"_app_ Term\""
  t2_type <- getState
  keyword ")"
  case t1_type of
   (Function t11 t12) -> if t11 == t2_type
                         then setState t12 >> return (Application t1 t2)
                         else fail $ "Mismatch types for function application \n" ++
                                     "function argument type: " ++ show t11 ++ "\n" ++
                                     "argument type : " ++ show t2_type 
   otherwise -> fail $ "Expecting Function type for the first term" ++
                        "of an application, receieved: " ++ show t1_type

abstraction :: ParsecT String Type IO Term
abstraction = try $ do
  keyword "abs"
  keyword "("
  iden <- identifier
  keyword ":"
  iden_type <- identifierType
  keyword "."
  setState identifierType
  t <- term
  t_type <- getState
  keyword ")"
  setState $ Function iden_type t_type
  return $ Abstraction iden t

identifier = undefined

identifierType = undefined

term = undefined
