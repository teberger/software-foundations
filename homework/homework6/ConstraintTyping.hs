module ConstraintTyping where

import qualified Syntax as S
import qualified Unification as U

import Control.Monad.State.Lazy
import Control.Monad as M 

type IdentifierTable = [] (S.Identifier, S.Type)
type TypeConstraint = (S.Type, S.Type)
type TypeConstraintSet = [] TypeConstraint
type TypeSubstitution = []  (S.Identifier, S.Type)

--reconstructType :: S.Term -> Maybe S.Term
reconstructType t = 
  let
    t0 = evalState (incVarTypes (evalLets t)) 0
    (constraints, _) = evalState (deriveTypeConstraints t0) (0, [])
    unifencoding = encode constraints
    (unifoutcome, unifsolvedequations) = U.unify unifencoding
  in
   case unifoutcome of
    U.Success ->
      let typesubst = decode unifsolvedequations
          t' = appSubs typesubst t0
      in Just t'
    U.HaltWithFailure -> Nothing
    U.HaltWithCycle -> Nothing


appSubs :: TypeSubstitution -> S.Term -> S.Term
appSubs subs (S.Abs id id_type term) = S.Abs id
                                       (replaceTypes subs id_type)
                                       (appSubs subs term)
appSubs subs (S.App t1 t2) = S.App (appSubs subs t1) (appSubs subs t2)
appSubs subs (S.If t1 t2 t3) = S.If (appSubs subs t1) (appSubs subs t2) (appSubs subs t3)
appSubs subs (S.Succ t) = S.Succ (appSubs subs t)
appSubs subs (S.Pred t) = S.Pred (appSubs subs t)
appSubs subs (S.IsZero t) = S.IsZero (appSubs subs t)
appSubs subs (S.Fix t) = S.Fix (appSubs subs t)
appSubs _ t = t

replaceTypes :: TypeSubstitution -> S.Type -> S.Type
replaceTypes subs (S.TypeVar id) = case lookup id subs of
                                    Just a -> a
                                    Nothing -> S.TypeVar id
replaceTypes s (S.TypeArrow t1 t2) = S.TypeArrow (replaceTypes s t1) (replaceTypes s t2)
replaceTypes _ t = t

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
  put (i+1, (id, id_type):ls)
  (set, rtype) <- deriveTypeConstraints t
  (j, _) <- get
  put (j, ls)
  return $ (set, S.TypeArrow id_type rtype)
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
  case lookup id ls of
   Just a -> return $ ([], a)
   Nothing -> fail $ "Could not find identifier: " ++ id ++
              "'s type. Perhaps an error in the source?"

evalLets :: S.Term -> S.Term 
evalLets (S.Let id t1 t2) = evalLets $ S.betaReduc id t1 t2
evalLets (S.App t1 t2) = S.App (evalLets t1) (evalLets t2)
evalLets (S.Abs id id_type t) = S.Abs id id_type (evalLets t)
evalLets (S.If t1 t2 t3) = S.If (evalLets t1) (evalLets t2) (evalLets t3)
evalLets (S.Fix t) = S.Fix (evalLets t)
evalLets (S.Succ t) = S.Succ (evalLets t)
evalLets (S.Pred t) = S.Pred (evalLets t)
evalLets (S.IsZero t) = S.IsZero (evalLets t)
-- is a value
evalLets t = t


incTypes :: S.Type -> State Integer S.Type
incTypes (S.TypeArrow t1 t2) = do
  t1' <- incTypes t1
  t2' <- incTypes t2
  return $ S.TypeArrow t1' t2'
incTypes (S.TypeVar v) = do
  i <- get
  put (i+1)
  return $ S.TypeVar (show i ++ v)
incTypes t = return t

incVarTypes :: S.Term -> State Integer S.Term
incVarTypes (S.App t1 t2) = do
  t1' <- incVarTypes t1
  t2' <- incVarTypes t2
  return $ S.App t1' t2'
incVarTypes (S.Abs id id_type t) = do
  id_type' <- incTypes id_type
  t' <- incVarTypes t
  return $ S.Abs id id_type' t'
incVarTypes (S.If t1 t2 t3) = do
  t1' <- incVarTypes t1
  t2' <- incVarTypes t2
  t3' <- incVarTypes t3  
  return $ S.If t1' t2' t3
incVarTypes (S.Fix t) = do
  t' <- incVarTypes t
  return $ S.Fix t'
incVarTypes (S.Succ t) = do
  t' <- incVarTypes t
  return $ S.Succ t'
incVarTypes (S.Pred t) = do
  t' <- incVarTypes t
  return $ S.Pred t'
incVarTypes (S.IsZero t) = do
  t' <- incVarTypes t
  return $ S.IsZero t'
-- is a value
incVarTypes t = return t
  

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
