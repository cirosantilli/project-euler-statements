import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P71

def betterFrac (a b c d : Nat) : Bool :=
  a * d > c * b

def isReduced (n d : Nat) : Bool :=
  decide (Nat.gcd n d = 1)

def leftOf (limit : Nat) (num den : Nat) : Nat :=
  let rec go (d bestN bestD : Nat) : Nat :=
    if d = 0 then bestN else
    let (bestN', bestD') :=
      (List.range d).foldl (fun acc n =>
        if decide (n < d) && isReduced n d && decide (n * den < num * d) then
          if betterFrac n d acc.1 acc.2 then (n, d) else acc
        else acc) (bestN, bestD)
    go (d - 1) bestN' bestD'
  go limit 0 1

def naive (limit : Nat) : Nat :=
  leftOf limit 3 7

example : naive 8 = 2 := by
  native_decide

end ProjectEulerStatements.P71
