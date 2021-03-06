module UnificationTests where

import Unification

t1 = Var "X" :: Term String String
t2 = Var "Y" :: Term String String
test_1 = unify [(t1, t2)] 

t3 = Var "Z" :: Term String String
test_2 = unify [(t1, t2), (t1, t3)] 

t4 = Fun "f" [t1]
test_3 = unify [(t1, t2), (t3, t4)]

test_4 = unify [(t1, t3), (t3, t4)]

test_5 = unify [(t4, t3)]

t6 = Fun "f" [t2]
test_6 = unify [(t4, t6)]

t7 = Fun "g" [t2]
test_7 = unify [(t4, t7)]

t11 = Fun "g" [Var "X2"]
s11 = Var "X1"
t12 = Fun "f" [Var "X1", Fun "h" [Var "X1"], Var "X2"]
s12 = Fun "f" [Fun "g" [Var "X3"], Var "X4", Var "X3"]
t1_problem = [(t11, s11), (t12, s12)]
test1 = unify t1_problem

-- test1 output : (Success, [
--                   (Var "X4",Fun "h" [Fun "g" [Var "X3"]]),
--                   (Var "X2",Var "X3"),
--                   (Var "X1",Fun "g" [Var "X2"])
-- ])

s21 = Fun "f" [Fun "g" [Fun "a" [], Var "X"], Fun "h" [Fun "f" [Var "Y", Var "Z"]]]
s22 = Fun "g" [Var "Y", Fun "h" [Fun "f" [Var "Z", Var "U"]]]
t21 = Fun "f" [Var "U", Fun "h" [Fun "f" [Var "X", Var "X"]]]
t22 = Fun "g" [Fun "f" [Fun "h" [Var "X"], Fun "a" []], Fun "h" [Fun "f" [Fun "a" [], Fun "b" []]]]
t2_problem = [(s21, t21), (s22, t22)]
test2 = unify t2_problem

-- test2 output : (HaltWithCycle,[(Var "X",Fun "f" [Fun "h" [Var "X"],Fun "a" []])])

s31 = Fun "f" []
t31 = Fun "g" [Var "A"] 
t3_problem = [(s31, t31)]
test3 = unify t3_problem

-- test3 output: (HaltWithFailure,[(Fun "f" [],Fun "g" [Var "A"])])

s41 = Fun "f" [Var "A"]
t41 = Fun "f" [Fun "g" [Var "A"]]
t4_problem = [(s41, t41)]
test4 = unify t4_problem

-- test4 output: (HaltWithCycle,[(Var "A",Fun "g" [Var "A"])])


-- reconstructType $ S.Let "double" (S.IAbs "f" (S.IAbs "a" (S.App (S.Var "f") (S.App (S.Var "f") (S.Var "a"))))) (S.Let "a" (S.App (S.App (S.Var "double") (S.Abs "x" S.TypeNat (S.Succ (S.Succ (S.Var "x"))))) (S.Succ S.Zero)) (S.Let "b" (S.App (S.App (S.Var "double") (S.Abs "x" S.TypeBool (S.Var "x"))) S.Fls) (S.If (S.Var "b") (S.Var "a") (S.Zero))))
