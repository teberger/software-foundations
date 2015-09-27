module Main where

import System.Environment (getArgs)
import System.IO (hGetContents, openFile, IOMode (ReadMode))

import Control.Monad (liftM)
import qualified Data.List as L

main :: IO ()
main = do
  undefined

data T = Leaf | TNode T T

data P = GoLeft P | GoRight P | This deriving Show

{- Section 2.1: Binary Trees -}

allPaths :: T -> [P]
allPaths (TNode t1 t2) = This : map GoLeft (allPaths t1) ++ map GoRight (allPaths t2)
allPaths Leaf = [This]


{- Section 2.2: General Trees -}
data Tree a = Node a [Tree a] deriving Show

foldTree :: (a -> [b] -> b) -> Tree a -> b
foldTree f (Node a subtrees) = f a $ (map (foldTree f) subtrees)

mapTree :: (a -> b) -> Tree a -> Tree b
mapTree f = foldTree (Node . f)


skeleton :: Show b => (String -> [b]) -> IO ()
skeleton fun = do
  [f,_] <- getArgs
  openFile f ReadMode >>= hGetContents >>= mapM_ print . fun

{- Section 2.3: Files -}
cat :: IO ()
cat = skeleton lines

tac :: IO ()
tac = skeleton (reverse . lines)

rev :: IO ()
rev = skeleton (map reverse . lines)

sort :: IO ()
sort = do 
  files <- getArgs
  content <- liftM concat $ mapM (\f -> hGetContents =<< openFile f ReadMode) files
  mapM_ print (L.sort $ lines content)

{- Section 2.4: Drawing -}
type Point = (Float, Float)
type Path = [Point]

makeCommand :: [Path] -> String
makeCommand paths = header paths ++ "\n" ++ (concatMap toPost paths) ++ "showpage\n%%EOF"
  where header :: [Path] -> String
        header paths = "%! PS-Adobe-3.0 EPSF-3.0\n%%BoundingBox: "
                       ++ show left ++ " "
                       ++ show bottom ++ " "
                       ++ show right ++ " "
                       ++ show top ++ "\n"

        bottom, top, left, right :: Float
        bottom = foldl1 min $ map (foldl1 min) $ map (map snd) paths
        top = foldl1 max $ map (foldl1 max) $ map (map snd) paths
        left = fst $ foldl1 min $ map (foldl1 min) paths
        right = fst $ foldl1 max $ map (foldl1 max) paths

        toPost :: Path -> String
        toPost ((x,y):ps) =
          (show x ++ " " ++ show y ++ " moveto\n") ++
          concatMap (\(x,y) -> show x ++ " " ++ show y ++ " lineto\n") ps
          ++ "closepath\nstroke\n\n"
