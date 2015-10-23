module LambdaCalculus where

import Text.Parsec
import Text.Parsec.Char
import Text.ParserCombinators.Parsec.Char

type VarName = String

data LambdaCalculus = Term | Value

data Term = Variable VarName |
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

constant :: ParsecT String TypeContext IO ConstantValue
constant = try $ whitespace >>
           (tru <|> fls <|> zero <?> "Constant value")
  
tru :: ParsecT String TypeContext IO ConstantValue
tru = try (string "tru" >> return Tru)

fls :: ParsecT String TypeContext IO ConstantValue
fls = try (string "fls" >> return Fls)

zero :: ParsecT String TypeContext IO ConstantValue
zero = try (string "0" >> return Zero)

succ :: ParsecT String TypeContext IO ConstantValue
succ = try $ do
  string "succ"
  whitespace
  t <- between (char '(') (char ')') term
  return t



term = undefined
