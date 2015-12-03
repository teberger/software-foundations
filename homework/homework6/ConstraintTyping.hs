module ConstraintTyping where

import qualified Syntax as S
import qualified Unification as U

import Control.Monad.State.Lazy
import Data.List as L 

type IdentifierTable = [] (S.Identifier, S.Type)
type TypeConstraint = (S.Type, S.Type)
type TypeConstraintSet = [] TypeConstraint
type TypeSubstitution = []  (S.Identifier, S.Type)

reconstructType :: S.Term -> Maybe S.Term
reconstructType t = 
  let
    (constraints, _) = evalState (deriveTypeConstraints t) (0, [])
    unifencoding = encode constraints
    (unifoutcome, unifsolvedequations) = U.unify unifencoding
  in
   case unifoutcome of
    U.Success ->
      let typesubst = decode unifsolvedequations
          t' = applyTypeSubstitutionToTerm typesubst t
      in Just t'
    U.HaltWithFailure -> Nothing
    U.HaltWithCycle -> Nothing

-- TODO TODO
applyTypeSubstitutionToTerm :: TypeSubstitution -> S.Term -> S.Term
applyTypeSubstitutionToTerm _ t = t

-- TAPL: Pg 322
deriveTypeConstraints :: S.Term -> State (Integer, IdentifierTable) (TypeConstraintSet, S.Type)
--Zero
deriveTypeConstraints S.Zero = return ([], S.TypeNat)
deriveTypeConstraints S.Tru = return ([], S.TypeBool)
deriveTypeConstraints S.Fls = return ([], S.TypeBool)
deriveTypeConstraints (S.Succ t) = do
  (set, rtype) <- deriveTypeConstraints t
  return $ ((rtype, S.TypeNat) :set, S.TypeNat)
--Pred t
deriveTypeConstraints (S.Pred t) = do
  (set, rtype) <- deriveTypeConstraints t
  return $ ((rtype, S.TypeNat) :set, S.TypeNat)
-- IsZero t 
deriveTypeConstraints (S.IsZero t) = do
  (set, rtype) <- deriveTypeConstraints t
  return $ ((rtype, S.TypeNat) :set, S.TypeBool)
-- If t1 t2 t3  
deriveTypeConstraints (S.If t1 t2 t3) = do
  (s1, r1) <- deriveTypeConstraints t1
  (s2, r2) <- deriveTypeConstraints t2
  (s3, r3) <- deriveTypeConstraints t3
  return $ ([(r2, r3), (r1, S.TypeBool)] ++ s1 ++ s2 ++ s3, r2)
-- Abs id id_type t
deriveTypeConstraints (S.Abs id id_type t) = do
  (i, ls) <- get
  put (i, (id, id_type):ls)
  (set, rtype) <- deriveTypeConstraints t
  (j, _) <- get
  put (j, ls)
  return $ (set, S.TypeArrow id_type rtype)
deriveTypeConstraints (S.IAbs id t) = do
  (i, ls) <- get
  let absType = S.TypeVar ('X':show i)
  put (i+1, (id, absType):ls)
  (set, rtype) <- deriveTypeConstraints t
  (j, _) <- get
  put (j, ls)
  return $ (set, S.TypeArrow absType rtype)
deriveTypeConstraints (S.Let id t1 t2) = deriveTypeConstraints (S.betaReduc id t1 t2)
-- App t1 t2
deriveTypeConstraints (S.App t1 t2) = do
  (s1, r1) <- deriveTypeConstraints t1
  (s2, r2) <- deriveTypeConstraints t2
  (i, ls) <- get
  put (i+1, ls)
  let rtype = S.TypeVar ('X':show i)
  return $ ((r1, S.TypeArrow r2 rtype) : s1 ++ s2, rtype)
-- Fix t1 t2
deriveTypeConstraints (S.Fix t) = do
  (set, S.TypeArrow f g) <- deriveTypeConstraints t
  return $ (set, f)
-- Var id
deriveTypeConstraints (S.Var id) = do
  (_, ls) <- get
  case L.lookup id ls of
   Just a -> return $ ([], a)
   Nothing -> fail $ "Could not find identifier: " ++ id ++
              "'s type. Perhaps an error in the source?"
  
type TypeUnifVar = S.Identifier
data TypeUnifFun =
  TypeUnifArrow |
  TypeUnifBool |
  TypeUnifNat  deriving (Show, Eq)

encode :: TypeConstraintSet -> [U.Equation TypeUnifVar TypeUnifFun]
encode = map (\(tau1, tau2) -> (enctype tau1, enctype tau2))
  where
    enctype :: S.Type -> U.Term TypeUnifVar TypeUnifFun
    enctype (S.TypeArrow tau1 tau2) = U.Fun TypeUnifArrow [enctype tau1, enctype tau2]
    enctype S.TypeBool = U.Fun TypeUnifBool []
    enctype S.TypeNat = U.Fun TypeUnifNat []
    enctype (S.TypeVar xi) = U.Var xi

decode :: [U.Equation TypeUnifVar TypeUnifFun] -> TypeSubstitution
decode = map f
  where
    f :: (U.Term TypeUnifVar TypeUnifFun, U.Term TypeUnifVar TypeUnifFun)
      -> (S.Identifier, S.Type)
    f (U.Var xi, t) = (xi, g t)
    g :: U.Term TypeUnifVar TypeUnifFun -> S.Type
    g (U.Fun TypeUnifArrow [t1, t2]) = S.TypeArrow (g t1) (g t2)
    g (U.Fun TypeUnifBool []) = S.TypeBool
    g (U.Fun TypeUnifNat []) = S.TypeNat
    g (U.Var xi) = S.TypeVar xi
