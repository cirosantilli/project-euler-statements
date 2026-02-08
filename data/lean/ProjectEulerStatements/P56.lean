import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P56

/-- Sum of decimal digits. -/
def digitSum (n : Nat) : Nat :=
  (Nat.digits 10 n).sum

/-- Maximum digit sum of `a^b` for `a,b < n`. -/
def naive (n : Nat) : Nat :=
  (List.range n).foldl (fun acc a =>
    (List.range n).foldl (fun acc2 b =>
      let s := digitSum (a ^ b)
      if s > acc2 then s else acc2) acc) 0

end ProjectEulerStatements.P56
