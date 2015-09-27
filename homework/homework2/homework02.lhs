\documentclass{article}
\usepackage{amsmath}

\begin{document}
\section{}
\subsection{Binary Trees}
> data T = Leaf | Node T T
> data P = GoLeft P | GoRight P | This
> 
> allPaths :: T -> [P]
> allPaths (Node t1 t2) = This : map GoLeft (allPaths t1)
>                         ++ map GoRight (allPaths t2)
> allPaths Leaf = [This]

\subsection{General Trees}
> data Tree a = Node a [Tree a]
> 
> foldTree :: (a -> [b] -> b) -> Tree a -> b
> foldTree f = (Node a subtrees) = f a $ map (foldtree f) subtrees
> 
> mapTree :: (a -> b) -> Tree a -> Tree b
> mapTree f = foldTree (Node . f)


\subsection{File Handling}
> import System.Environment (getArgs)
> import System.IO (hGetContents, openFile, IOMode (ReadMode))
> 
> skeleton :: Show b => (a -> b) -> IO ()
> skeleton fun = do
>   [f,_] <- getArgs
>   openFile f ReadMode >>= hGetContents >>= mapM_ print . fun

> cat :: IO ()
> cat = skeleton lines
> 
> tac :: IO ()
> tac = skeleton (reverse . lines)
> 
> rev :: IO ()
> rev = skeleton (map reverse . lines)

> sort :: IO ()
> sort = do 
>   files <- getArgs
>   content <- liftM concat $ mapM (\f -> hGetContents =<< openFile f ReadMode) files
>   mapM_ print (L.sort $ lines content)


\subsection{Drawing \& Postscript}
> type Point = (Float, Float)
> type Path = [Point]
> 
> makeCommand :: [Path] -> String
> makeCommand paths = header paths ++ "\n" ++ (concatMap toPost paths) ++ "showpage\n%%EOF"
>   where header :: [Path] -> String
>         header paths = "%! PS-Adobe-3.0 EPSF-3.0\n%%BoundingBox: "
>                        ++ show left ++ " "
>                        ++ show bottom ++ " "
>                        ++ show right ++ " "
>                        ++ show top ++ "\n"
> 
>         bottom, top, left, right :: Float
>         bottom = foldl1 min $ map (foldl1 min) $ map (map snd) paths
>         top = foldl1 max $ map (foldl1 max) $ map (map snd) paths
>         left = fst $ foldl1 min $ map (foldl1 min) paths
>         right = fst $ foldl1 max $ map (foldl1 max) paths
> 
>         toPost :: Path -> String
>         toPost ((x,y):ps) =
>           (show x ++ " " ++ show y ++ " moveto\n") ++
>           concatMap (\(x,y) -> show x ++ " " ++ show y ++ " lineto\n") ps
>           ++ "closepath\nstroke\n\n"

\subsection{Proofs}


> foldr :: (a -> b -> b) -> b -> [a] -> b
> foldl :: (b -> a -> b) -> b -> [a] -> b
> foldr f x ls = foldl (flip f) x (reverse ls)
> 
> f :: (a -> b -> b)
> (flip f) :: (b -> a -> b)
> 
> foldr f x [] = x
> foldl (flip f) x (reverse []) = x
> 
> 
assume this is true, as the inductive hypothesis
> foldr f x ls = foldl (flip f) x ls = c
> 
> foldr f x (l:ls)             = foldl (flip f) x (reverse (l:ls))
>                              = foldl (flip f) x ((reverse ls) ++ [l])
> f (foldr f x ls) l           = (flip f) l $ foldl (flip f) x (reverse ls)
> f c l                        = (flip f) l c


\end{document}
