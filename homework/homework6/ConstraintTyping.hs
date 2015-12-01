module ConstraintTyping where

import qualified Syntax as S
import qualified Unification as U

type TypeConstraint = (S.Type, S.Type)
type TypeConstraintSet = [] TypeConstraint
type TypeSubstitution = []  (S.Identifier, S.Type)

reconstructType :: S.Term -> Maybe S.Term
reconstructType t = 
  let
    constraints = deriveTypeConstraints t
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

type TypeUnifVar = S.Identifier
data TypeUnifFun =
  TypeUnifArrow |
  TypeUnifBool |
  TypeUnifNat  deriving (Show, Eq)


-- TODO TODO TODO TODO 
applyTypeSubstitutionToTerm = undefined
deriveTypeConstraints = undefined

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
