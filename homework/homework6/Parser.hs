module Parser where

import Prelude hiding (succ, pred)

import Text.Parsec
import Text.Parsec.Char
import Text.ParserCombinators.Parsec.Char

import Syntax

returnType = "_"

whitespace :: Monad m => ParsecT String () m ()
whitespace = spaces >> return ()

keyword :: Monad m => String -> ParsecT String () m ()
keyword p = try $ do
  whitespace
  string p <?> ("Expecting keyword: " ++ p)
  whitespace

tru :: Monad m => ParsecT String () m Term
tru = keyword "true" >> return Tru

fls :: Monad m => ParsecT String () m Term
fls = keyword "false" >> return Fls
      
zero :: Monad m => ParsecT String () m Term
zero = keyword "0" >> return Zero

iszero :: Monad m => ParsecT String () m Term
iszero = try $ do
  keyword "iszero"
  keyword "("
  t <- term <?> "Error parsing: Succ ( Term ), expected Term but failed"
  keyword ")"
  return (IsZero t)

succ :: Monad m => ParsecT String () m Term
succ = try $ do
  keyword "succ"
  keyword "("
  t <- term <?> "Error parsing: Succ ( Term ), expected Term but failed"
  keyword ")"
  return (Succ t)

pred :: Monad m => ParsecT String () m Term 
pred = try $ do
  keyword "pred"
  keyword "("
  t <- term <?> "Error parsing: Pred ( Term ), expected Term but failed"
  keyword ")"
  return (Pred t)

if_statement :: Monad m => ParsecT String () m Term
if_statement = try $ do
  keyword "if"
  cond <- term <?> "Expecting 'term' following _if_"
  keyword "then"
  t_then <- term <?> "Expecting 'term' following _then_"
  keyword "else"
  t_else <- term <?> "Expecting 'term' following _else_"
  keyword "fi"
  return (If cond t_then t_else)

application :: Monad m => ParsecT String () m Term
application = try $ do
  keyword "app"
  keyword "("
  t1 <- term <?> "Error parsing first 'term' following _app_"
  keyword ","
  t2 <- term <?> "Error parsing second 'term' following \"_app_ Term\""
  keyword ")"
  return (App t1 t2)

poly_let :: Monad m => ParsecT String () m Term
poly_let = do
  keyword "let"
  iden <- identifier
  keyword "="
  t1 <- term
  keyword "in"
  t2 <- term
  return $ Let iden t1 t2

abstraction :: Monad m => ParsecT String () m Term
abstraction = exp_abstraction <|> imp_abstraction

imp_abstraction :: Monad m => ParsecT String () m Term
imp_abstraction = do
  keyword "abs"
  keyword "("
  iden <- identifier
  keyword "."
  t <- term
  keyword ")"
  return $ IAbs iden t

exp_abstraction :: Monad m => ParsecT String () m Term
exp_abstraction = try $ do
  keyword "abs"
  keyword "("
  iden <- identifier
  keyword ":"
  iden_type <- identifierType
  keyword "."
  t <- term
  keyword ")"
  return $ Abs iden iden_type t

fix :: Monad m => ParsecT String () m Term
fix = try $ do
  keyword "fix"
  keyword "("
  t <- term
  keyword ")"
  return $ Fix t

identifier :: Monad m => ParsecT String () m String
identifier = try $ do
  whitespace
  x <- many letter
  case all (x /=) ["succ", "pred", "if", "fi", "arr", "Bool", "Nat",
                   "abs", "app", "true", "false", "then", "else",
                   "iszero", "fix", "let", "in" ,""]
    of
   True -> do
     return x
   otherwise -> fail $ "Could not parse an identifier, must not be a reserved" ++
                       " word or contain anything but characters: " ++ x

identifier_term :: Monad m => ParsecT String () m Term
identifier_term = identifier >>= return . Var
  
term :: Monad m => ParsecT String () m Term
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

-- typing information and ------------------------------------------------------
identifierType :: Monad m => ParsecT String () m Type
identifierType = boolType <|> natType <|> functionType <|> varType
                 <?> "identifier type parser"

boolType :: Monad m => ParsecT String () m Type
boolType = keyword "Bool" >> return TypeBool

natType :: Monad m => ParsecT String () m Type
natType = keyword "Nat" >> return TypeNat

varType :: Monad m => ParsecT String () m Type
varType = many letter >>= return . TypeVar

functionType :: Monad m => ParsecT String () m Type
functionType = try $ do
  keyword "arr"
  keyword "("
  t1 <- identifierType
  keyword ","
  t2 <- identifierType
  keyword ")"
  return $ TypeArrow t1 t2
