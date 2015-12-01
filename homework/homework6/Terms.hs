module Terms where


data Term v f = Fun f [Term v f] |
                Var v

type Equation v f = (Term v f, Term f v)

type Binding v f  = (v, Term v f)

type Substitution v f = [Binding v f]

data EquationOutcome = HaltFailure |
                       HaltCycle |
                       NoMatch |
                       Success deriving (Show, Eq)

