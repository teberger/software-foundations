let double = abs (f . abs (a. app (f,  app (f, a))))
in a = app ( app (double, abs(f : Nat . succ(succ(f)))) , 1)
in b = app ( app (double, abs(f : Bool . f)) , 1)
in if b then a else 0
