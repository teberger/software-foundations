\documentclass{article}
\usepackage{amsmath}
\usepackage[margin=1in]{geometry}

%include lhs2TeX.fmt
%include polycode.fmt

% options ghci -fglasgow-exts

\begin{document}
\title{Homework 04 : CS 558}
\author{Taylor Berger}
\maketitle

\section{Type Unification Algorithm}

The direct translation of the type unification algorithm in TAPL
separates the pairs of terms in four different patterns.
> unify :: (Eq v, Eq f) => [Equation v f] -> (Outcome, [Equation v f])
> unify = unify' []
>   where
If there are no more equations to unify, we have been successful.
>     unify' sigma [] = (Success, sigma)
If the equation to unify is of the form \verb|X = Y| then move that
equation into the solution set, substitute all X with Y, and unify the rest of the equations
>     unify' sigma (s@(Var v1, Var v2):eqns) = if  v1 == v2
>                                              then unify' sigma eqns -- delete identity
>                                              else unify' (s:sigma) $
>                                                     applySubst' eqns [(v1, Var v2)]
If the equation looks like \verb|X = f(Y1,...,Yn)| then move that
equation to the solution set, substitute all X with \verb|f(Y1,...,Yn)| and unify the
rest of the equations. If the right hand side mentions the variable named on the left
hand side, we delcare a failure due to a cycle.
>     unify' sigma (s@(Var v, t):eqns) = if inVars v t
>                                         then (HaltWithCycle, [s])
>                                         else unify' (s:sigma) $
>                                                applySubst' eqns [(v, t)]
This case allows us to flip the equation around freely if the right hand side is variable
and the left had side is not.
>     unify' sigma ((t, Var v):eqns) = unify' sigma ((Var v, t):eqns) -- flip 
And finally, if the equation is of the form \verb|f(X1...Xn) = f(Y1...Yn)| then remove
the function and add in all equations where we set the pairs of variables equal to
each other. However, if the functions are not the same functions we declare failure. 
>     unify' sigma (s@(Fun f terms_1, Fun g terms_2):eqns) = if  f == g
>                                                          then unify' sigma $
>                                                                 (zip terms_1 terms_2) ++ eqns
>                                                          else (HaltWithFailure, [s])

\subsection{Unification Testing}
Each of the small tests are designed to test on particular aspect of the unification algorithm.
the large tests are examples from class or the book to ensure the algorithms works as a whole.

\subsubsection{\verb|X = Y| test case}
> t1 = Var "X"
> t2 = Var "Y"
> test_1 = unify [(t1, t2)]

Output:
> (Success,[(Var "X",Var "Y")])

\subsubsection{Substitution of Variables}
Expanding on the previous test:
> t3 = Var "Z" :: Term String String
> test_2 = unify [(t1, t2), (t1, t3)]

Output:
> (Success,[(Var "Y",Var "Z"),(Var "X",Var "Y")])

\subsubsection{Variable Functions}
> t4 = Fun "f" [t1]
> test_3 = unify [(t1, t2), (t3, t4)] 

Output: 
> (Success,[(Var "Z",Fun "f" [Var "Y"]),(Var "X",Var "Y")])

\subsubsection{Testing for Cycle detection}
> test_5 = test_3 = unify [(t1, t3), (t3, t4)]

Output:
> (HaltWithCycle,[(Var "Z",Fun "f" [Var "Z"])])

\subsubsection{Flipping}
> test_5 = unify [(t4, t3)]

Output:
> (Success,[(Var "Z",Fun "f" [Var "X"])])

\subsubsection{Matching Functions}
> t6 = Fun "f" [t2]
> test_6 = unify [(t4, t6)]

Output:
> (Success,[(Var "X",Var "Y")])

\subsection{MisMatch Functions}
> t7 = Fun "g" [t2]
> test_7 = unify [(t4, t7)]

Output:
> (HaltWithFailure,[(Fun "f" [Var "X"],Fun "g" [Var "Y"])])


\subsubsection{Large Tests (1)}
> t11 = Fun "g" [Var "X2"]
> s11 = Var "X1"
> t12 = Fun "f" [Var "X1", Fun "h" [Var "X1"], Var "X2"]
> s12 = Fun "f" [Fun "g" [Var "X3"], Var "X4", Var "X3"]
> t1_problem = [(t11, s11), (t12, s12)]
> test1 = unify t1_problem

Output:
> (Success,[(Var "X4",Fun "h" [Fun "g" [Var "X3"]]),(Var "X2",Var "X3"),(Var "X1",Fun "g" [Var "X2"])])

Yielding the equations:
> X4 = h(g(X3))
> X2 = X3
> X1 = g(X2)

\subsubsection{Large Tests (2)}
> s21 = Fun "f" [Fun "g" [Fun "a" [], Var "X"], Fun "h" [Fun "f" [Var "Y", Var "Z"]]]
> s22 = Fun "g" [Var "Y", Fun "h" [Fun "f" [Var "Z", Var "U"]]]
> t21 = Fun "f" [Var "U", Fun "h" [Fun "f" [Var "X", Var "X"]]]
> t22 = Fun "g" [Fun "f" [Fun "h" [Var "X"], Fun "a" []], Fun "h" [Fun "f" [Fun "a" [], Fun "b" []]]]
> t2_problem = [(s21, t21), (s22, t22)]
> test2 = unify t2_problem

Output:
> (HaltWithCycle,[(Var "X",Fun "f" [Fun "h" [Var "X"],Fun "a" []])])

Yielding the Error in equations:
> X = f(h(X), a())

\section{Constraint Typing}
To reconstruct they types, given the code in the homework writeup, we define
the deriveTypeConstraints function which operates in the domain of the State monad.
The functions for this were the converted constraint typing rules in Types and
Programming Languages on Page 322. 

> -- TAPL: Pg 322
> deriveTypeConstraints :: S.Term -> State (Integer, IdentifierTable) (TypeConstraintSet, S.Type)
> deriveTypeConstraints S.Zero = return ([], S.TypeNat)
> deriveTypeConstraints S.Tru = return ([], S.TypeBool)
> deriveTypeConstraints S.Fls = return ([], S.TypeBool)
> deriveTypeConstraints (S.Succ t) = do
>   (set, rtype) <- deriveTypeConstraints t
>   return $ ((rtype, S.TypeNat) :set, S.TypeNat)
> deriveTypeConstraints (S.Pred t) = do
>   (set, rtype) <- deriveTypeConstraints t
>   return $ ((rtype, S.TypeNat) :set, S.TypeNat)
> deriveTypeConstraints (S.IsZero t) = do
>   (set, rtype) <- deriveTypeConstraints t
>   return $ ((rtype, S.TypeNat) :set, S.TypeBool)
> deriveTypeConstraints (S.If t1 t2 t3) = do
>   (s1, r1) <- deriveTypeConstraints t1
>   (s2, r2) <- deriveTypeConstraints t2
>   (s3, r3) <- deriveTypeConstraints t3
>   return $ ([(r2, r3), (r1, S.TypeBool)] ++ s1 ++ s2 ++ s3, r2)
> deriveTypeConstraints (S.Abs id id_type t) = do
>   (i, ls) <- get
>   put (i, (id, id_type):ls)
>   (set, rtype) <- deriveTypeConstraints t
>   (j, _) <- get
>   put (j, ls)
>   return $ (set, S.TypeArrow id_type rtype)
> deriveTypeConstraints (S.App t1 t2) = do
>   (s1, r1) <- deriveTypeConstraints t1
>   (s2, r2) <- deriveTypeConstraints t2
>   (i, ls) <- get
>   put (i+1, ls)
>   let rtype = S.TypeVar ('X':show i)
>   return $ ((r1, S.TypeArrow r2 rtype) : s1 ++ s2, rtype)
> deriveTypeConstraints (S.Fix t) = do
>   (set, S.TypeArrow f g) <- deriveTypeConstraints t
>   return $ (set, f)
> deriveTypeConstraints (S.Var id) = do
>   (_, ls) <- get
>   case lookup id ls of
>    Just a -> return $ ([], a)
>    Nothing -> fail $ "Could not find identifier: " ++ id ++
>               "'s type. Perhaps an error in the source?"


\section{Let Polymorphism and Implicit Types}

\end{document}
