\documentclass{article}
%include lhs2TeX.fmt

\begin{document}
\section{List Manipulation}
\subsection{Swap}
> swap :: [] a -> [] a
> swap ls = undefined

\subsection{Sets}
>
>setUnion :: [Integer] -> [Integer] -> [Integer]
>setUnion = (.) . (.) nub (++)
>
>setIntersection :: [Integer] -> [Integer] -> [Integer]
>setIntersection s1 s2 = [a | a <- s1, not (elem a s2)]
>
>xor True True = False
>xor False False = False
>xor _ _ = True
>
>setDifference :: [] a -> [] a -> [] a
>setDifference s1 s2 = [x | x <- setUnion s1 s2, xor (elem x s1) (elem x s2)]
>
>setEqual :: [] a -> [] a -> Bool
>setEqual s1 s2 = and [elem x s1 && elem x s2 | x <- setUnion s1 s2]
>
>powerSet :: [] a -> [] ([] a)
>powerset [] = [[]]
>powerSet (x:xs) = rest ++ (map (x:) rest)
>  where rest = powerset xs
\end{document}