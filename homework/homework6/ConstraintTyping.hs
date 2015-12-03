module ConstraintTyping where

import qualified Syntax as S
import qualified Unification as U

import Control.Monad.State.Lazy
import Data.List as L 

type IdentifierTable = [] (S.Identifier, S.Type)
type TypeConstraint = (S.Type, S.Type)
type TypeConstraintSet = [] TypeConstraint
type TypeSubstitution = []  (S.Identifier, S.Type)

--reconstructType :: S.Term -> Maybe S.Term
reconstructType t = 
  let
    constraints = evalState (deriveTypeConstraints t) (0, [])
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

increment :: State (Integer, [] (S.Identifier, S.Type)) Integer
increment = do
  (i, ls) <- get
  put ((i+1), ls)
  return i 

-- TODO TODO
deriveTypeConstraints :: S.Term -> State (Integer, IdentifierTable) TypeConstraintSet
--Zero
deriveTypeConstraints S.Zero = do
  i <- increment
  return . return $ (S.TypeVar ('X':show i), S.TypeNat)
--Tru 
deriveTypeConstraints S.Tru = do
  i <- increment
  return . return $ (S.TypeVar ('X':show i), S.TypeBool)
--Fls
deriveTypeConstraints S.Fls = do
  i <- increment
  return . return $ (S.TypeVar ('X':show i), S.TypeBool) 
--Succ t 
deriveTypeConstraints (S.Succ t) = do
  set <- deriveTypeConstraints t
  i <- increment
  return $ (S.TypeVar ('X':show i), S.TypeNat) :set
--Pred t
deriveTypeConstraints (S.Pred t) = do
  set <- deriveTypeConstraints t
  i <- increment
  return $ (S.TypeVar ('X':show i), S.TypeNat) :set
-- IsZero t 
deriveTypeConstraints (S.IsZero t) = do
  set <- deriveTypeConstraints t
  i <- increment
  return $ (S.TypeVar ('X':show i), S.TypeBool) :set
-- If t1 t2 t3  
deriveTypeConstraints (S.If t1 t2 t3) = do
  o1@(s1:_) <- deriveTypeConstraints t1
  o2@(s2:_) <- deriveTypeConstraints t2
  o3@(s3:_) <- deriveTypeConstraints t3
  return $ [(snd s2, snd s3), (snd s1, S.TypeBool)] ++ o1 ++ o2 ++ o3
-- Abs id id_type t
deriveTypeConstraints (S.Abs id id_type t) = do
  (i, ls) <- get
  put (i, (id, id_type):ls)
  s@(s1:set) <- deriveTypeConstraints t
  j <- increment
  return $ (S.TypeVar ('X':show j), S.TypeArrow id_type (snd s1)) : set
-- App t1 t2
deriveTypeConstraints (S.App t1 t2) = do
  o1@(s1:_) <- deriveTypeConstraints t1
  o2@(s2:_) <- deriveTypeConstraints t2
  i <- increment
  return $ (snd s1, S.TypeArrow
                      (snd s2)
                      (S.TypeVar ('X':show i)))
         : o1 ++ o2
-- Fix t1 t2
deriveTypeConstraints (S.Fix t) = do
  o1@((_,S.TypeArrow f g):_) <- deriveTypeConstraints t
  i <- increment
  return $ (S.TypeVar ('X':show i), f) : o1
-- Var id
deriveTypeConstraints (S.Var id) = do
  i <- increment
  (_, ls) <- get
  case L.lookup id ls of
   Just a -> return $ return (S.TypeVar ('X':show i), a)
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
