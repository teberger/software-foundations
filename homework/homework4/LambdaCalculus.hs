module LambdaCalculus where

import Text.Parsec
import Text.Parsec.Char
import Text.ParserCombinators.Parsec.Char

type VarName = String

data LambdaCalculus = Term | Value

--data Term = Variable Value | 
--            Abstraction VarName Type Term |
--            Application Term Term

data Term = TermValue Value |
            Abstraction VarName Type Term |
            Application Term Term |
            Constant ConstantValue |
            If Term Term Term |
            Succ Term |
            Pred Term |
            IsZero Term 

data ConstantValue = Tru | Fls | Zero deriving (Show, Eq, Enum)

data Value = ConstantValue |
             AbstractionValue VarName Type Term |
             Numeric Term

data Type = Function Type Type |
            Bool |
            Nat

data TypeContext = Empty |
                   Ext (VarName, Type) TypeContext

whitespace = spaces <|> (many tab >> return ())
killwhite p = whitespace >> p >>= (\x -> whitespace >> return x)
maybebetween c1 p c2 = try (between (char c1) (char c2) p <|> p)



constant :: ParsecT String TypeContext IO Term
constant = try $ killwhite
           (tru <|> fls <|> zero <|> number <?> "Constant value")

number :: ParsecT String TypeContext IO Term
number = try $ do
  whitespace
  z <- try (zero <|> (string "succ" >>
                      (maybebetween '(' number ')') >>=
                      (return . Succ)))
  return z

tru :: ParsecT String TypeContext IO Term
tru = try (killwhite (string "tru"))
      >> return (Constant Tru)

fls :: ParsecT String TypeContext IO Term
fls = try (killwhite (string "fls"))
      >> return (Constant Fls)

zero :: ParsecT String TypeContext IO Term
zero = try (killwhite (string "0"))
       >> return (Constant Zero)

iszero :: ParsecT String TypeContext IO Term
iszero = try $ do
  killwhite $ string "iszero"
  t <- killwhite $ maybebetween '(' term ')'
  return $ IsZero t

succ :: ParsecT String TypeContext IO Term
succ = try $ do
  killwhite $ string "succ"
  t <- killwhite $ maybebetween '(' term ')'
  return (Succ t)

pred :: ParsecT String TypeContext IO Term
pred = try $ do
  killwhite $ string "pred"
  t <- killwhite $ maybebetween '(' term ')'
  return (Pred t)

if_statement :: ParsecT String TypeContext IO Term
if_statement = try $ do
  killwhite $ string "if"
  t1 <- killwhite $ maybebetween '(' term ')'
  string "then"
  t2 <- killwhite $ maybebetween '(' term ')'
  string "else"
  t3 <- killwhite $ maybebetween '(' term ')'
  killwhite $ string "fi"
  return $ If t1 t2 t3


term = undefined
