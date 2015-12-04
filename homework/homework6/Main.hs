module Main where

import System.Environment (getArgs)
import System.IO (openFile, hGetContents, IOMode(ReadMode))

import Data.Either (Either(Left, Right))

import Text.Parsec (runParser)

import Parser
import Evaluator
import Syntax

main :: IO ()
main = do
  args <- getArgs
  case length args /= 1 of
   True -> putStrLn help
   otherwise -> parseLC args

parseLC :: [String] -> IO ()
parseLC (filename:_) = do
  contents <- hGetContents =<< openFile filename ReadMode
  case runParser start 0 filename contents of
   Left err -> print err
   Right term -> do
     putStrLn $ "Syntax Correct. \n\tResult type: " -- ++ show (term_type)
--     putStrLn $ "Evaluating...\n\tResult: " ++ show (eval term)

help :: String
help = "Program requires only 1 argument. Usage: \n" ++
       "  TLBN <filename>"
