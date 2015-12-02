module Unification where

import Data.List (lookup)

data Term v f =
  Fun f [Term v f] |
  Var v
  deriving Show

data Outcome =
  HaltWithFailure |
  HaltWithCycle |
  Success |
  NoMatch
  deriving Show

type Equation v f = (Term v f, Term v f)
type Binding v f  = (v, Term v f)
type Substitution v f = [Binding v f]

applySubst :: (Eq v, Eq f) => Term v f -> Substitution v f -> Term v f
applySubst (Var x) theta =
  case lookup x theta of
   Just a -> a
   Nothing -> Var x 
applySubst (Fun f tlist) theta =
  Fun f $ map (\x -> applySubst x theta) tlist


applySubst' :: (Eq v, Eq f) => [Equation v f] -> Substitution v f -> [Equation v f]
applySubst' eq1 theta = map (\(s,t) -> (applySubst s theta, applySubst t theta)) eq1


unify :: (Eq v, Eq f) => [Equation v f] -> (Outcome, [Equation v f])
unify = unify' []
  where
    unify' :: (Eq v, Eq f) => [Equation v f] -> [Equation v f] -> (Outcome, [Equation v f])
    unify' sigma [] = (Success, sigma)
    unify' sigma (theta:eqns) = case theta of
      s@(Var v1, Var v2) -> if v1 == v2
                            then unify' sigma eqns -- delete identity
                            else unify' (s:sigma) $ applySubst' eqns [(v1, Var v2)]
      s@(Var v, t) -> if inVars v t
                      then (HaltWithCycle, [s])
                      else unify' (s:sigma) $ applySubst' eqns [(v, t)]
      (t, Var v) -> unify' sigma ((Var v, t):eqns) -- flip 
      (Fun f terms_1, Fun g terms_2) -> if f == g
                                        then unify' sigma $ (zip terms_1 terms_2) ++ eqns
                                        else (HaltWithFailure, [theta])

inVars :: Eq v => v -> Term v f -> Bool
inVars v0 (Var v1) = v1 == v0
inVars v0 (Fun f vs) = any (inVars v0) vs 
