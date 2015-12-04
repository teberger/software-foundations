module Main where

import System.Environment (getArgs)
import System.IO (openFile, hGetContents, IOMode(ReadMode))

import Data.Either (Either(Left, Right))

import Text.Parsec (runParser)
import Control.Monad.State.Lazy

import ConstraintTyping
import Parser
import Evaluator as E
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
  case runParser term 0 filename contents of
   Left err -> print err
   Right term -> do
     putStrLn "\nSyntax Correct. Typing..."
     case reconstructType term of
      Just t' -> do
        putStrLn $ "\tResult type: " ++ show (evalState (E.evalType t') [])
        putStrLn $ "Evaluating...\n\tResult: " ++ show (E.eval t')
      Nothing -> putStrLn "Could not reconstruct type"

help :: String
help = "Program requires only 1 argument. Usage: \n" ++
       "  TLBN <filename>"
