module Main where

import System.Environment (getArgs)
import System.IO (openFile, hGetContents, IOMode(ReadMode))

import Data.Map (singleton) 
import Data.Either (Either(Left, Right))

import Text.Parsec (runParser)

import LcParser
import LcEvaluator

main :: IO ()
main = do
  args <- getArgs
  case length args /= 1 of
   True -> putStrLn help
   otherwise -> parseLC args

parseLC :: [String] -> IO ()
parseLC (filename:_) = do
  contents <- hGetContents =<< openFile filename ReadMode
  case runParser term (singleton returnType NullType) filename contents of
   Left err -> print err
   Right answer -> print $ eval answer

help :: String
help = "Program requires only 1 argument. Usage: \n" ++
       "  TLBN <filename>"
