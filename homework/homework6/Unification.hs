module Unification where

import Data.List (lookup)

data Term v f =
  Fun f [Term v f] |
  Var v

data Outcome =
  HaltWithFailure |
  HaltWithCycle |
  Success |
  NoMatch 

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
unify = undefined
