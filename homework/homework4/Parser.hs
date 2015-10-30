module LcParser where

import Text.Parsec
import Text.ParserCombinators.Parsec.Char

import Control.Monad.Identity


data LambdaCalculus = LC 
data LambdaValue = LV

zero :: ParsecT String LambdaCalculus IO LambdaValue
zero = do
  t <- spaces
  return LV
