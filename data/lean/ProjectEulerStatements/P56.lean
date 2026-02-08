import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P56

/-- Sum of decimal digits. -/
def digitSum (n : Nat) : Nat :=
  (Nat.digits 10 n).sum

/-- Maximum digit sum of `a^b` for `a,b < 100`. -/
def naive : Nat :=
  (List.range 100).foldl (fun acc a =>
    (List.range 100).foldl (fun acc2 b =>
      let s := digitSum (a ^ b)
      if s > acc2 then s else acc2) acc) 0

end ProjectEulerStatements.P56
