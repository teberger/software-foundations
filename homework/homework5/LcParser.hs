module LcParser where

import Prelude hiding (succ, pred)

import Control.Monad.Trans (liftIO)

import Text.Parsec
import Text.Parsec.Char
import Text.ParserCombinators.Parsec.Char

import qualified Data.Map.Strict as M

import LcData

returnType = "_"

whitespace :: Monad m => ParsecT String TypeContext m ()
whitespace = spaces >> return ()

keyword :: Monad m => String -> ParsecT String TypeContext m ()
keyword p = try $ do
  whitespace
  string p <?> ("Expecting keyword: " ++ p)
  whitespace

merge :: VarName -> Type -> TypeContext -> TypeContext
merge name t context = M.insert name t context

getReturnState :: Monad m => ParsecT String TypeContext m Type
getReturnState = do
  gamma <- getState
  return $ gamma M.! returnType

tru :: Monad m => ParsecT String TypeContext m Term
tru = try $ do
  keyword "true"
  modifyState $ merge returnType Boole
  return Tru

fls :: Monad m => ParsecT String TypeContext m Term
fls = try $ do
  keyword "false"
  modifyState $ merge returnType Boole
  return Fls
      
zero :: Monad m => ParsecT String TypeContext m Term
zero = try $ do
  keyword "0"
  modifyState $ merge returnType Nat
  return Zero

iszero :: Monad m => ParsecT String TypeContext m Term
iszero = try $ do
  keyword "iszero"
  keyword "("
  t <- term <?> "Error parsing: Succ ( Term ), expected Term but failed"
  t_type <- getReturnState
  if t_type == Nat 
  then do
    keyword ")"
    -- change the state from Nat to Boole
    modifyState $ merge returnType Boole
    return (IsZero t)
  else 
    fail $ "Expected type 'Nat' in iszero but was " ++ show t_type

succ :: Monad m => ParsecT String TypeContext m Term
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
    fail $ "Expected type 'Nat' in 'Succ' but was " ++ show t_type

pred :: Monad m => ParsecT String TypeContext m Term 
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
    fail $ "Expected type 'Nat' in 'Pred' but was " ++ show t_type

if_statement :: Monad m => ParsecT String TypeContext m Term
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
      modifyState $ merge returnType then_type 
      return (If cond t_then t_else)
    else 
      fail $ "Type inconsistency for then/else parts of if statement\n" ++
             "then type: " ++ (show then_type) ++ "\n" ++
             "else type: " ++ (show else_type) ++ "\n"


application :: Monad m => ParsecT String TypeContext m Term
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
                           modifyState $ merge returnType t12
                           return (Application t1 t2)
                         else fail $ "Mismatch types for function application\n"
                                     ++ "function argument required type: "
                                     ++ show t11 ++ "\n"
                                     ++ "actual argument type : "
                                     ++ show t2_type 
   otherwise -> fail $ "Expecting Function type for the first term" ++
                        "of an application, receieved: " ++ show t1_type

abstraction :: Monad m => ParsecT String TypeContext m Term
abstraction = try $ do
  keyword "abs"
  keyword "("

  iden <- identifier
  keyword ":"

  iden_type <- identifierType
  keyword "."
  
  modifyState $ merge iden iden_type

  t <- term
  t_type <- getReturnState 

  keyword ")"
  modifyState $ merge returnType (Function iden_type t_type)
  modifyState $ M.delete iden 
  return $ Abstraction iden t

fix :: Monad m => ParsecT String TypeContext m Term
fix = try $ do
  keyword "fix"
  keyword "("
  t <- term
  t_type <- getReturnState
  case t_type of
   (Function a b) -> do
     keyword ")"
     modifyState $ merge returnType a
     return $ Fix t
   otherwise -> fail $ "Fail, expected a function type for 'Fix' but found " ++
                       (show t_type)

identifier :: Monad m => ParsecT String TypeContext m String
identifier = try $ do
  whitespace
  x <- many letter
  case all (x /=) ["succ", "pred", "if", "fi", "arr", "Bool", "Nat",
                   "abs", "app", "true", "false", "then", "else",
                   "iszero", "fix", ""]
    of
   True -> do
     return x
   otherwise -> fail $ "Could not parse an identifier, must not be a reserved" ++
                       " word or contain anything but characters: " ++ x

identifier_term :: Monad m => ParsecT String TypeContext m Term
identifier_term = try $ do
  x <- identifier

  context <- getState
  case M.lookup x context of
   Just t -> modifyState $ merge returnType t
   Nothing -> fail $ "Identifier: " ++ x ++ " has no type in current typing context"
  
  return $ Identifier x
  
term :: Monad m => ParsecT String TypeContext m Term
term = 
  identifier_term <|>
  fix <|>
  abstraction <|>
  application <|>
  tru <|>
  fls <|>
  if_statement <|>
  zero <|>
  succ <|>
  pred <|>
  iszero <|>
  -- a term in parens
  (try (keyword "(" >> term >>= \k -> keyword ")" >> return k))
  <?> "Basic term parsing"

start :: Monad m => ParsecT String TypeContext m (Term, Type)
start = do
  t <- term
  term_type <- getReturnState
  return (t, term_type)

-- typing information and ------------------------------------------------------
identifierType :: Monad m => ParsecT String TypeContext m Type
identifierType = boolType <|> natType <|> functionType
                 <?> "identifier type parser"

boolType :: Monad m => ParsecT String TypeContext m Type
boolType = try $ keyword "Bool" >> return Boole

natType :: Monad m => ParsecT String TypeContext m Type
natType = try $ keyword "Nat" >> return Nat

functionType :: Monad m => ParsecT String TypeContext m Type
functionType = try $ do
  keyword "arr"
  keyword "("
  t1 <- identifierType
  keyword ","
  t2 <- identifierType
  keyword ")"
  return $ Function t1 t2
