module LambdaCalculus where

import Text.Parsec
import Text.Parsec.Char
import Text.ParserCombinators.Parsec.Char

import qualified Data.Map.Strict as M

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


type TypeContext = M.Map VarName Type

returnType = "_"

merge :: VarName -> Type -> TypeContext -> TypeContext
merge = undefined

getReturnState :: ParsecT String TypeContext IO Type
getReturnState = do
  gamma <- getState
  return $ gamma M.! returnType

whitespace = many (spaces <|> (many tab >> return ())) >> return ()

keyword p = try $ do
  whitespace
  string p <?> ("Expecting keyword: " ++ p)
  whitespace

tru :: ParsecT String TypeContext IO Term
tru = try $ do
  keyword "tru"
  updateState $ merge returnType Boole
  return Tru

fls :: ParsecT String TypeContext IO Term
fls = try $ do
  keyword "fls"
  updateState $ merge returnType Boole
  return Fls
      
zero :: ParsecT String TypeContext IO Term
zero = try $ do
  keyword "0"
  updateState $ merge returnType Boole
  return Zero

iszero :: ParsecT String TypeContext IO Term
iszero = try $ do
  keyword "iszero"
  keyword "("
  t <- term <?> "Error parsing: Succ ( Term ), expected Term but failed"
  t_type <- getReturnState
  if t_type == Nat --TODO fix ths
  then do
    keyword ")"
    -- change the state from Nat to Boole
    updateState $ merge returnType Boole
    return (IsZero t)
  else 
    fail $ "Expected type 'Nat' but was " ++ show t_type

succ :: ParsecT String TypeContext IO Term
succ = try $ do
  keyword "succ"
  keyword "("
  t <- term <?> "Error parsing: Succ ( Term ), expected Term but failed"
  t_type <- getReturnState
  if t_type == Nat
  then do
    -- no need to change the state, it is the same
    keyword ")"
    return (Succ t)
  else 
    fail $ "Expected type 'Nat' but was " ++ show t_type

pred :: ParsecT String TypeContext IO Term 
pred = try $ do
  keyword "pred"
  keyword "("
  t <- term <?> "Error parsing: Pred ( Term ), expected Term but failed"
  t_type <- getReturnState
  if t_type == Nat
  then do
    -- no need to change the state, it is the same
    keyword ")"
    return (Pred t)
  else 
    fail $ "Expected type 'Nat' but was " ++ show t_type

if_statement :: ParsecT String TypeContext IO Term
if_statement = try $ do
  keyword "if"
  cond <- term <?> "Expecting 'term' following _if_"
  cond_type <- getReturnState
  if cond_type /= Boole
  then
    fail $ "Expecting Boolean type for if-statement conditional, received: " ++
           show cond_type
  else do
    keyword "then"
    t_then <- term <?> "Expecting 'term' following _then_"
    then_type <- getReturnState

    keyword "else"
    t_else <- term <?> "Expecting 'term' following _else_"
    else_type <- getReturnState
    keyword "fi"

    if then_type == else_type
    then do
      updateState $ merge returnType then_type 
      return (If cond t_then t_else)
    else 
      fail $ "Type inconsistency for then/else parts of if statement\n" ++
             "then type: " ++ (show then_type) ++ "\n" ++
             "else type: " ++ (show else_type) ++ "\n"


application :: ParsecT String TypeContext IO Term
application = try $ do
  keyword "app"
  keyword "("
  t1 <- term <?> "Error parsing first 'term' following _app_"
  t1_type <- getReturnState
  keyword ","
  t2 <- term <?> "Error parsing second 'term' following \"_app_ Term\""
  t2_type <- getReturnState
  keyword ")"
  case t1_type of
   (Function t11 t12) -> if t11 == t2_type
                         then do
                           updateState $ merge returnType t12
                           return (Application t1 t2)
                         else fail $ "Mismatch types for function application\n"
                                     ++ "function argument required type: "
                                     ++ show t11 ++ "\n"
                                     ++ "actual argument type : "
                                     ++ show t2_type 
   otherwise -> fail $ "Expecting Function type for the first term" ++
                        "of an application, receieved: " ++ show t1_type

abstraction :: ParsecT String TypeContext IO Term
abstraction = try $ do
  keyword "abs"
  keyword "("

  iden <- identifier
  keyword ":"

  iden_type <- identifierType
  keyword "."
  
  updateState $ merge iden iden_type

  t <- term
  t_type <- getReturnState 

  keyword ")"
  updateState $ merge returnType (Function iden_type t_type)
  updateState $ M.delete iden 
  return $ Abstraction iden t


--TODO: Just these two now and testing
identifier :: ParsecT String TypeContext IO String
identifier = undefined
  
term :: ParsecT String TypeContext IO Term
term = undefined


-- typing information and ------------------------------------------------------
identifierType :: ParsecT String TypeContext IO Type
identifierType = boolType <|> natType <|> functionType
                 <?> "identifier type parser"

boolType :: ParsecT String TypeContext IO Type
boolType = try $ keyword "Bool" >> return Boole

natType :: ParsecT String TypeContext IO Type
natType = try $ keyword "Nat" >> return Nat

functionType :: ParsecT String TypeContext IO Type
functionType = try $ do
  keyword "arr"
  keyword "("
  t1 <- identifierType
  keyword ","
  t2 <- identifierType
  keyword ")"
  return $ Function t1 t2

