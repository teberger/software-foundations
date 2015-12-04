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

Each function sets the second par to of the tuple to the constraint-based
return type and the first part of the tuple to be any type constraints
generated by the rules. Each is a direct translation of the rules in
TAPL, so there's not much explanation past that.

\subsection{Constraint Typing Testing}
To test, the parser and type checker were updated to fit with the refactoring
necessary for this version of the homework. So all inputs are written in files,
parsed, then passed to the type reconstruction algorithm. We used many of the
examples from the last homework.

\subsection{IsEven 3}
\begin{verbatim}
[taylor@localhost homework6]$ ./lceval iseven.TLBN 

Syntax Correct. Typing...
	Result type: TypeNat
Evaluating...
	Result: False
\end{verbatim}



\subsection{\verb|exp 2 3|}
\begin{verbatim}
[taylor@localhost homework6]$ ./lceval exp1.TLBN 

Syntax Correct. Typing...
	Result type: TypeNat
Evaluating...
	Result: 9
\end{verbatim}

\subsection{\verb|fact (fact 3)|}
\begin{verbatim}
[taylor@localhost homework6]$ ./lceval fact3.TLBN 

Syntax Correct. Typing...
	Result type: TypeNat
Evaluating...
	Result: 720
\end{verbatim}

\section{Let Polymorphism and Implicit Types}
To introduce implicit typing we just have to modify the parser
to generate a fresh, generic type var for the implicitly typed
abstraction. Therefore, the parser for abstractions is modified
seen below:
> abstraction :: Monad m => ParsecT String Integer m Term
> abstraction = exp_abstraction <|> imp_abstraction

> imp_abstraction :: Monad m => ParsecT String Integer m Term
> imp_abstraction = do
>   keyword "abs"
>   keyword "("
>   iden <- identifier
>   keyword "."
>   t <- term
>   keyword ")"
>   i <- getState
>   putState (i+1)
>   return $ Abs iden (TypeVar ('X':show i)) t

> exp_abstraction :: Monad m => ParsecT String Integer m Term
> exp_abstraction = try $ do
>   keyword "abs"
>   keyword "("
>   iden <- identifier
>   keyword ":"
>   iden_type <- identifierType
>   keyword "."
>   t <- term
>   keyword ")"
>   return $ Abs iden iden_type t

Where we now offer the choice to parse an implicitly or explicitly typed abstraction.
In the case of the implicitly typed abstraction, we generate a new, fresh variable
stored in the parser state.


\subsection{Polymorphic Let}
To introduce polymorphic let statements, we update the data constuctor and parser for
Terms to include the let statement:

> data Term =
>   ...
>   Let Identifier Term Term |
>   ...

Parser: 

> poly_let :: Monad m => ParsecT String Integer m Term
> poly_let = do
>   keyword "let"
>   iden <- identifier
>   keyword "="
>   t1 <- term
>   keyword "in"
>   t2 <- term
>   return $ Let iden t1 t2


Subsequently, in typing, we must provide the evaluation of lets using the poly-let
constraint typing rule. We modify the reconstructType function to transform the
let-statements into their appropriate reductions (and update the new type variables
to be different than others):
> reconstructType :: S.Term -> Maybe S.Term
> reconstructType t = 
>   let
>     t0 = evalState (incVarTypes (evalLets t)) 0
>     (constraints, _) = evalState (deriveTypeConstraints t0) (0, [])
>     unifencoding = encode constraints
>     (unifoutcome, unifsolvedequations) = U.unify unifencoding
>   in

Where \emph{evalLets} and \emph{incVarTypes} can be found in the appendix.

\subsection{Testing}
To test the poly-let and implicitly typed abstractions, we an example from
the book that should unify correctly:

\begin{verbatim}
let double = abs (f . abs (a. app (f,  app (f, a)))) in
let a = app ( app (double, abs(f : Nat . succ(succ(f)))) , 0) in
let b = app ( app (double, abs(f : Bool . f)) , false) in
if b then a else 0 fi
\end{verbatim}

Which, evaluates to:
\begin{verbatim}
[taylor@localhost homework6]$ ./lceval poly-double.TLBN 

Syntax Correct. Typing...
	Result type: TypeNat
Evaluating...
	Result: 0
\end{verbatim}

\newpage
\section*{Appendix}
\subsection{Parser.hs}
> module Parser where

> import Prelude hiding (succ, pred)

> import Text.Parsec
> import Text.Parsec.Char
> import Text.ParserCombinators.Parsec.Char

> import Syntax

> whitespace :: Monad m => ParsecT String Integer m ()
> whitespace = spaces >> return ()

> keyword :: Monad m => String -> ParsecT String Integer m ()
> keyword p = try $ do
>   whitespace
>   string p <?> ("Expecting keyword: " ++ p)
>   whitespace

> tru :: Monad m => ParsecT String Integer m Term
> tru = keyword "true" >> return Tru

> fls :: Monad m => ParsecT String Integer m Term
> fls = keyword "false" >> return Fls
>       
> zero :: Monad m => ParsecT String Integer m Term
> zero = keyword "0" >> return Zero

> iszero :: Monad m => ParsecT String Integer m Term
> iszero = try $ do
>   keyword "iszero"
>   keyword "("
>   t <- term <?> "Error parsing: Succ ( Term ), expected Term but failed"
>   keyword ")"
>   return (IsZero t)

> succ :: Monad m => ParsecT String Integer m Term
> succ = try $ do
>   keyword "succ"
>   keyword "("
>   t <- term <?> "Error parsing: Succ ( Term ), expected Term but failed"
>   keyword ")"
>   return (Succ t)

> pred :: Monad m => ParsecT String Integer m Term 
> pred = try $ do
>   keyword "pred"
>   keyword "("
>   t <- term <?> "Error parsing: Pred ( Term ), expected Term but failed"
>   keyword ")"
>   return (Pred t)

> if_statement :: Monad m => ParsecT String Integer m Term
> if_statement = try $ do
>   keyword "if"
>   cond <- term <?> "Expecting 'term' following _if_"
>   keyword "then"
>   t_then <- term <?> "Expecting 'term' following _then_"
>   keyword "else"
>   t_else <- term <?> "Expecting 'term' following _else_"
>   keyword "fi"
>   return (If cond t_then t_else)

> application :: Monad m => ParsecT String Integer m Term
> application = try $ do
>   keyword "app"
>   keyword "("
>   t1 <- term <?> "Error parsing first 'term' following _app_"
>   keyword ","
>   t2 <- term <?> "Error parsing second 'term' following \"_app_ Term\""
>   keyword ")"
>   return (App t1 t2)

> poly_let :: Monad m => ParsecT String Integer m Term
> poly_let = do
>   keyword "let"
>   iden <- identifier
>   keyword "="
>   t1 <- term
>   keyword "in"
>   t2 <- term
>   return $ Let iden t1 t2

> abstraction :: Monad m => ParsecT String Integer m Term
> abstraction = exp_abstraction <|> imp_abstraction

> imp_abstraction :: Monad m => ParsecT String Integer m Term
> imp_abstraction = do
>   keyword "abs"
>   keyword "("
>   iden <- identifier
>   keyword "."
>   t <- term
>   keyword ")"
>   i <- getState
>   putState (i+1)
>   return $ Abs iden (TypeVar ('X':show i)) t

> exp_abstraction :: Monad m => ParsecT String Integer m Term
> exp_abstraction = try $ do
>   keyword "abs"
>   keyword "("
>   iden <- identifier
>   keyword ":"
>   iden_type <- identifierType
>   keyword "."
>   t <- term
>   keyword ")"
>   return $ Abs iden iden_type t

> fix :: Monad m => ParsecT String Integer m Term
> fix = try $ do
>   keyword "fix"
>   keyword "("
>   t <- term
>   keyword ")"
>   return $ Fix t

> identifier :: Monad m => ParsecT String Integer m String
> identifier = try $ do
>   whitespace
>   x <- many letter
>   case all (x /=) ["succ", "pred", "if", "fi", "arr", "Bool", "Nat",
>                    "abs", "app", "true", "false", "then", "else",
>                    "iszero", "fix", "let", "in" ,""]
>     of
>    True -> do
>      return x
>    otherwise -> fail $ "Could not parse an identifier, must not be a reserved" ++
>                        " word or contain anything but characters: " ++ x

> identifier_term :: Monad m => ParsecT String Integer m Term
> identifier_term = identifier >>= return . Var
>   
> term :: Monad m => ParsecT String Integer m Term
> term = 
>   identifier_term <|>
>   poly_let <|>
>   fix <|>
>   abstraction <|>
>   application <|>
>   tru <|>
>   fls <|>
>   if_statement <|>
>   zero <|>
>   succ <|>
>   pred <|>
>   iszero <|>
>   -- a term in parens
>   (try (keyword "(" >> term >>= \k -> keyword ")" >> return k))
>   <?> "Basic term parsing"

> -- typing information and ------------------------------------------------------
> identifierType :: Monad m => ParsecT String Integer m Type
> identifierType = boolType <|> natType <|> functionType <|> varType
>                  <?> "identifier type parser"

> boolType :: Monad m => ParsecT String Integer m Type
> boolType = keyword "Bool" >> return TypeBool

> natType :: Monad m => ParsecT String Integer m Type
> natType = keyword "Nat" >> return TypeNat

> varType :: Monad m => ParsecT String Integer m Type
> varType = many letter >>= return . TypeVar

> functionType :: Monad m => ParsecT String Integer m Type
> functionType = try $ do
>   keyword "arr"
>   keyword "("
>   t1 <- identifierType
>   keyword ","
>   t2 <- identifierType
>   keyword ")"
>   return $ TypeArrow t1 t2


\subsection{Evaluator.hs}
> module Evaluator where 

> import Syntax
> import Data.List (delete)
> import Control.Monad.State.Lazy

> evalType :: Term -> State [(Identifier, Type)] Type
> evalType (Abs id id_type t) = do
>   types <- get
>   let t_type = (id, id_type)
>   put (t_type:types)
>   r <- evalType t 
>   put $ delete t_type types
>   return $ (TypeArrow id_type r)
> evalType (App t1 t2) = do 
>   t1' <- evalType t1
>   t2' <- evalType t2
>   case t1' of
>    (TypeArrow s1 s2) -> case s1 == t2' of
>      True -> return t2'
>      False -> fail "parameter types do no match"
>    otherwise -> fail "t1 not a function type"
> evalType (If t1 t2 t3) = do
>   t1_type <- evalType t1
>   t2_type <- evalType t2
>   t3_type <- evalType t3
>   case (t2_type == t3_type) && t1_type == TypeBool of
>    True -> return t2_type
>    False -> fail "t2 /= t3 or t1 not a bool" 
> evalType (Var v) = do
>   types <- get
>   case lookup v types of
>    Just a -> return a
>    Nothing -> fail ""
> evalType (Fix t) = do
>   t_type <- evalType t
>   case t_type of
>    (TypeArrow t1 t2) -> return $ t1
>    otherwise -> fail ""
> evalType (Succ t) = do
>   t_type <- evalType t
>   case t_type of
>    TypeNat -> return $ TypeNat
>    otherwise -> fail ""
> evalType (Pred t) = do
>   t_type <- evalType t
>   case t_type of
>    TypeNat -> return $ TypeNat
>    otherwise -> fail ""
> evalType (IsZero t) = do
>   t_type <- evalType t
>   case t_type of
>    TypeNat -> return $ TypeBool
>    otherwise -> fail ""
> evalType Zero = return TypeNat
> evalType Tru = return TypeBool
> evalType Fls = return TypeBool

> eval :: Term -> Term
> eval t = case eval1 t of
>           Just t1 -> eval t1
>           Nothing -> t

> eval1 :: Term -> Maybe Term
> eval1 t 
>   | isValue t = Nothing
>   | otherwise = case t of
>                  Fix t -> evalFix t
>                  App t1 t2 -> evalApplication t1 t2
>                  If t1 t2 t3 -> evalIf t1 t2 t3
>                  IsZero t -> evalIsZero t
>                  Succ t -> evalSucc t 
>                  Pred t -> evalPred t
>                  otherwise -> Nothing

> evalFix :: Term -> Maybe Term
> evalFix a@(Abs varname _ t) = Just $ betaReduc varname (Fix a) t
> evalFix t = eval1 t >>= return . Fix

> evalApplication :: Term -> Term -> Maybe Term
> evalApplication t1@(Abs name _ t) t2
>   | isValue t2 = Just (betaReduc name t2 t)
>   | otherwise = eval1 t2 >>= return . (App t1)
> evalApplication t1 t2
>   | isValue t1 = eval1 t2 >>= return . (App t1)
>   | otherwise = eval1 t1 >>= return . \t -> (App t t2)

> evalIf :: Term -> Term -> Term -> Maybe Term
> evalIf Tru t2 t3 = Just t2
> evalIf Fls t2 t3 = Just t3
> evalIf t1 t2 t3 = eval1 t1 >>= return . \t -> (If t t2 t3)

> evalSucc :: Term -> Maybe Term
> evalSucc t = eval1 t >>= Just . Succ

> evalPred :: Term -> Maybe Term
> evalPred (Succ t) = Just t
> evalPred Zero = Just Zero
> evalPred t = eval1 t >>= Just . Pred 

> evalIsZero :: Term -> Maybe Term
> evalIsZero Zero = Just Tru
> evalIsZero (Succ t)
>   | isNumeric t = Just Fls
>   | otherwise = Nothing
> evalIsZero t = eval1 t >>= Just . IsZero 
  

\subsection{Unification.hs}
> module Unification where

> import Data.List (find)

> data Term v f =
>   Fun f [Term v f] |
>   Var v
>   deriving Show

> data Outcome =
>   HaltWithFailure |
>   HaltWithCycle |
>   Success |
>   NoMatch
>   deriving Show

> type Equation v f = (Term v f, Term v f)
> type Binding v f  = (v, Term v f)
> type Substitution v f = [Binding v f]

> applySubst :: (Eq v, Eq f) => Term v f -> Substitution v f -> Term v f
> applySubst (Var x) theta =
>   case find (\(z,_) -> z == x) theta of
>    Just (_,a) -> a
>    Nothing -> Var x 
> applySubst (Fun f tlist) theta =
>   Fun f $ map (\x -> applySubst x theta) tlist


> applySubst' :: (Eq v, Eq f) => [Equation v f] -> Substitution v f -> [Equation v f]
> applySubst' eq1 theta = map (\(s,t) -> (applySubst s theta, applySubst t theta)) eq1


> unify :: (Eq v, Eq f) => [Equation v f] -> (Outcome, [Equation v f])
> unify = unify' []
>   where
>     unify' :: (Eq v, Eq f) => [Equation v f] -> [Equation v f] -> (Outcome, [Equation v f])
>     unify' sigma [] = (Success, sigma)
>     unify' sigma (s@(Var v1, Var v2):eqns) = if  v1 == v2
>                                              then unify' sigma eqns -- delete identity
>                                              else unify' (s:sigma) $
>                                                     applySubst' eqns [(v1, Var v2)]
>     unify' sigma (s@(Var v, t):eqns) = if inVars v t
>                                         then (HaltWithCycle, [s])
>                                         else unify' (s:sigma) $
>                                                applySubst' eqns [(v, t)]
>     unify' sigma ((t, Var v):eqns) = unify' sigma ((Var v, t):eqns) -- flip 
>     unify' sigma (s@(Fun f terms_1, Fun g terms_2):eqns) = if  f == g
>                                                          then unify' sigma $
>                                                                 (zip terms_1 terms_2) ++ eqns
>                                                          else (HaltWithFailure, [s])

> inVars :: Eq v => v -> Term v f -> Bool
> inVars v0 (Var v1) = v1 == v0
> inVars v0 (Fun f vs) = any (inVars v0) vs 

\subsection{ConstraintTyping.hs}
> module ConstraintTyping where

> import qualified Syntax as S
> import qualified Unification as U

> import Control.Monad.State.Lazy
> import Control.Monad as M 

> type IdentifierTable = [] (S.Identifier, S.Type)
> type TypeConstraint = (S.Type, S.Type)
> type TypeConstraintSet = [] TypeConstraint
> type TypeSubstitution = []  (S.Identifier, S.Type)

> reconstructType :: S.Term -> Maybe S.Term
> reconstructType t = 
>   let
>     t0 = evalState (incVarTypes (evalLets t)) 0
>     (constraints, _) = evalState (deriveTypeConstraints t0) (0, [])
>     unifencoding = encode constraints
>     (unifoutcome, unifsolvedequations) = U.unify unifencoding
>   in
>    case unifoutcome of
>     U.Success ->
>       let typesubst = decode unifsolvedequations
>           t' = appSubs typesubst t0
>       in Just t'
>     U.HaltWithFailure -> Nothing
>     U.HaltWithCycle -> Nothing

> appSubs :: TypeSubstitution -> S.Term -> S.Term
> appSubs subs (S.Abs id id_type term) = S.Abs id
>                                        (replaceTypes subs id_type)
>                                        (appSubs subs term)
> appSubs subs (S.App t1 t2) = S.App (appSubs subs t1) (appSubs subs t2)
> appSubs subs (S.If t1 t2 t3) = S.If (appSubs subs t1) (appSubs subs t2) (appSubs subs t3)
> appSubs subs (S.Succ t) = S.Succ (appSubs subs t)
> appSubs subs (S.Pred t) = S.Pred (appSubs subs t)
> appSubs subs (S.IsZero t) = S.IsZero (appSubs subs t)
> appSubs subs (S.Fix t) = S.Fix (appSubs subs t)
> appSubs _ t = t


> replaceTypes :: TypeSubstitution -> S.Type -> S.Type
> replaceTypes subs (S.TypeVar id) = case lookup id subs of
>                                     Just a -> a
>                                     Nothing -> S.TypeVar id
> replaceTypes s (S.TypeArrow t1 t2) = S.TypeArrow (replaceTypes s t1) (replaceTypes s t2)
> replaceTypes _ t = t


> -- TAPL: Pg 322
> deriveTypeConstraints :: S.Term -> State (Integer, IdentifierTable) (TypeConstraintSet, S.Type)
> deriveTypeConstraints S.Zero = return ([], S.TypeNat)
> deriveTypeConstraints S.Tru = return ([], S.TypeBool)
> deriveTypeConstraints S.Fls = return ([], S.TypeBool)
> deriveTypeConstraints (S.Succ t) = do
>   (set, rtype) <- deriveTypeConstraints t
>   return $ ((rtype, S.TypeNat) :set, S.TypeNat)
> --Pred t
> deriveTypeConstraints (S.Pred t) = do
>   (set, rtype) <- deriveTypeConstraints t
>   return $ ((rtype, S.TypeNat) :set, S.TypeNat)
> -- IsZero t 
> deriveTypeConstraints (S.IsZero t) = do
>   (set, rtype) <- deriveTypeConstraints t
>   return $ ((rtype, S.TypeNat) :set, S.TypeBool)
> -- If t1 t2 t3  
> deriveTypeConstraints (S.If t1 t2 t3) = do
>   (s1, r1) <- deriveTypeConstraints t1
>   (s2, r2) <- deriveTypeConstraints t2
>   (s3, r3) <- deriveTypeConstraints t3
>   let set = s1 ++ s2 ++ s3
>       rset = (r2, r3) : ((r1, S.TypeBool) : set)
>   return $ ( rset, r2 )
> deriveTypeConstraints (S.Abs id id_type t) = do
>   (i, ls) <- get
>   put (i+1, (id, id_type):ls)
>   (set, rtype) <- deriveTypeConstraints t
>   (j, _) <- get
>   put (j, ls)
>   return $ (set, S.TypeArrow id_type rtype)
> -- App t1 t2
> deriveTypeConstraints (S.App t1 t2) = do
>   (s1, r1) <- deriveTypeConstraints t1
>   (s2, r2) <- deriveTypeConstraints t2
>   (i, ls) <- get
>   put (i+1, ls)
>   let rtype = S.TypeVar ('X':show i)
>   return $ ((r1, S.TypeArrow r2 rtype) : s1 ++ s2, rtype)
> -- Fix t1 t2
> deriveTypeConstraints (S.Fix t) = do
>   (set, S.TypeArrow f g) <- deriveTypeConstraints t
>   return $ (set, f)
> -- Var id
> deriveTypeConstraints (S.Var id) = do
>   (_, ls) <- get
>   case lookup id ls of
>    Just a -> return $ ([], a)
>    Nothing -> fail $ "Could not find identifier: " ++ id ++
>               "'s type. Perhaps an error in the source?"

> evalLets :: S.Term -> S.Term 
> evalLets (S.Let id t1 t2) = evalLets $ S.betaReduc id t1 t2
> evalLets (S.App t1 t2) = S.App (evalLets t1) (evalLets t2)
> evalLets (S.Abs id id_type t) = S.Abs id id_type (evalLets t)
> evalLets (S.If t1 t2 t3) = S.If (evalLets t1) (evalLets t2) (evalLets t3)
> evalLets (S.Fix t) = S.Fix (evalLets t)
> evalLets (S.Succ t) = S.Succ (evalLets t)
> evalLets (S.Pred t) = S.Pred (evalLets t)
> evalLets (S.IsZero t) = S.IsZero (evalLets t)
> -- is a value
> evalLets t = t


> incTypes :: S.Type -> State Integer S.Type
> incTypes (S.TypeArrow t1 t2) = do
>   t1' <- incTypes t1
>   t2' <- incTypes t2
>   return $ S.TypeArrow t1' t2'
> incTypes (S.TypeVar v) = do
>   i <- get
>   put (i+1)
>   return $ S.TypeVar (show i ++ v)
> incTypes t = return t

> incVarTypes :: S.Term -> State Integer S.Term
> incVarTypes (S.App t1 t2) = do
>   t1' <- incVarTypes t1
>   t2' <- incVarTypes t2
>   return $ S.App t1' t2'
> incVarTypes (S.Abs id id_type t) = do
>   id_type' <- incTypes id_type
>   t' <- incVarTypes t
>   return $ S.Abs id id_type' t'
> incVarTypes (S.If t1 t2 t3) = do
>   t1' <- incVarTypes t1
>   t2' <- incVarTypes t2
>   t3' <- incVarTypes t3  
>   return $ S.If t1' t2' t3
> incVarTypes (S.Fix t) = do
>   t' <- incVarTypes t
>   return $ S.Fix t'
> incVarTypes (S.Succ t) = do
>   t' <- incVarTypes t
>   return $ S.Succ t'
> incVarTypes (S.Pred t) = do
>   t' <- incVarTypes t
>   return $ S.Pred t'
> incVarTypes (S.IsZero t) = do
>   t' <- incVarTypes t
>   return $ S.IsZero t'
> -- is a value
> incVarTypes t = return t
>   

> type TypeUnifVar = S.Identifier
> data TypeUnifFun =
>   TypeUnifArrow |
>   TypeUnifBool |
>   TypeUnifNat  deriving (Show, Eq)

> encode :: TypeConstraintSet -> [U.Equation TypeUnifVar TypeUnifFun]
> encode = map (\(tau1, tau2) -> (enctype tau1, enctype tau2))
>   where
>     enctype :: S.Type -> U.Term TypeUnifVar TypeUnifFun
>     enctype (S.TypeArrow tau1 tau2) = U.Fun TypeUnifArrow [enctype tau1, enctype tau2]
>     enctype S.TypeBool = U.Fun TypeUnifBool []
>     enctype S.TypeNat = U.Fun TypeUnifNat []
>     enctype (S.TypeVar xi) = U.Var xi

> decode :: [U.Equation TypeUnifVar TypeUnifFun] -> TypeSubstitution
> decode = map f
>   where
>     f :: (U.Term TypeUnifVar TypeUnifFun, U.Term TypeUnifVar TypeUnifFun)
>       -> (S.Identifier, S.Type)
>     f (U.Var xi, t) = (xi, g t)
>     g :: U.Term TypeUnifVar TypeUnifFun -> S.Type
>     g (U.Fun TypeUnifArrow [t1, t2]) = S.TypeArrow (g t1) (g t2)
>     g (U.Fun TypeUnifBool []) = S.TypeBool
>     g (U.Fun TypeUnifNat []) = S.TypeNat
>     g (U.Var xi) = S.TypeVar xi





\section{Main.hs}
> module Main where

> import System.Environment (getArgs)
> import System.IO (openFile, hGetContents, IOMode(ReadMode))

> import Data.Either (Either(Left, Right))

> import Text.Parsec (runParser)
> import Control.Monad.State.Lazy

> import ConstraintTyping
> import Parser
> import Evaluator as E
> import Syntax

> main :: IO ()
> main = do
>   args <- getArgs
>   case length args /= 1 of
>    True -> putStrLn help
>    otherwise -> parseLC args

> parseLC :: [String] -> IO ()
> parseLC (filename:_) = do
>   contents <- hGetContents =<< openFile filename ReadMode
>   case runParser term 0 filename contents of
>    Left err -> print err
>    Right term -> do
>      putStrLn "\nSyntax Correct. Typing..."
>      case reconstructType term of
>       Just t' -> do
>         putStrLn $ "\tResult type: " ++ show (evalState (E.evalType t') [])
>         putStrLn $ "Evaluating...\n\tResult: " ++ show (E.eval t')
>       Nothing -> putStrLn "Could not reconstruct type"

> help :: String
> help = "Program requires only 1 argument. Usage: \n" ++
>        "  TLBN <filename>"


\subsection{Syntax.hs}
> module Syntax where

> type Identifier = String

> data Type =
>   TypeArrow Type Type |
>   TypeVar Identifier |
>   TypeNat  |
>   TypeBool deriving (Show, Eq)
>   
> data Term =
>   Abs Identifier Type Term | 
>   Let Identifier Term Term | 
>   App Term Term | 
>   Var Identifier | 
>   Fix Term | 
>   If Term Term Term |
>   Succ Term | 
>   Pred Term | 
>   IsZero Term |
>   Zero |
>   Tru |
>   Fls deriving Eq

> instance Show Term where
>   show (Var name) = "Var " ++ name
>   show (Abs name t_type t) = "Abs " ++ name ++
>                            ": " ++ (show t_type) ++
>                            " (" ++ (show t) ++ ")"
>   show (Let id t1 t2) = "Let " ++ id ++ " = " ++ show t1 ++
>                         " in " ++ show t2
>   show (App t1 t2) = "App (" ++ (show t1) ++") ("++ (show t2) ++ ")"
>   show (If t1 t2 t3) = "If (" ++ show t1 ++
>                        ") then (" ++ show t2 ++
>                        ") else (" ++ show t3 ++
>                        ") fi"
>   show (Fix t) = "Fix (" ++ show t ++ ")"
>   show (Succ t) = if isNumeric t
>                   then show $ convertNumeric (Succ t)
>                   else "Succ (" ++ show t ++ ")"
>   show (Pred t) = "Pred (" ++ show t ++ ")"
>   show (IsZero t) = "IsZero (" ++ show t ++ ")"
>   show Tru = "True"
>   show Fls = "False"
>   show Zero = "0"
>   
> betaReduc :: Identifier -> Term -> Term -> Term
> betaReduc l r (Var name) = if name == l
>                            then r
>                            else (Var name)
> -- any var with this name is bound to a different abstraction and
> -- should not be replaced via the current beta reduction
> betaReduc l r (Abs id id_type term) = if id == l
>                                       then Abs id id_type term
>                                       else Abs id id_type (betaReduc l r term)
> betaReduc l r (Let id t1 t2) = if id == l
>                                then Let id t1 t2
>                                else Let id (betaReduc l r t1)
>                                            (betaReduc l r t2)
> betaReduc l r (App t1 t2) = App (betaReduc l r t1)
>                                 (betaReduc l r t2)
> betaReduc l r (If t1 t2 t3) = If (betaReduc l r t1)
>                                  (betaReduc l r t2)
>                                  (betaReduc l r t3)
> betaReduc l r (Succ t) = Succ (betaReduc l r t)
> betaReduc l r (Pred t) = Pred (betaReduc l r t)
> betaReduc l r (IsZero t) = IsZero (betaReduc l r t)
> betaReduc l r t = t

> {-
> | Determines if the value is a numeric value or not
> | Zero is always numeric
> | Succ v is numeric iff v is numeric
> | 
> --}
> isNumeric :: Term -> Bool
> isNumeric Zero = True
> isNumeric (Succ t) = isNumeric t
> isNumeric _ = False

> isValue :: Term -> Bool
> isValue Tru = True
> isValue Fls = True
> isValue (Var _) = True
> isValue (Abs _ _ _) = True
> isValue t = isNumeric t

> convertNumeric :: Term -> Int
> convertNumeric (Succ t) = 1 + convertNumeric t
> convertNumeric Zero = 0


\end{document}
