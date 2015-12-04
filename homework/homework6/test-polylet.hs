let double = abs (f . abs (a. app (f,  app (f, a)))) in
let a = app ( app (double, abs(f : Nat . succ(succ(f)))) , 0) in
let b = app ( app (double, abs(f : Bool . f)) , false) in
if b then a else 0 fi
