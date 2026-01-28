import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P16

def digitSum (n : Nat) : Nat :=
  (Nat.digits 10 n).sum

def naive (n : Nat) : Nat :=
  digitSum (2 ^ n)

example : naive 15 = 26 := by
  native_decide

end ProjectEulerStatements.P16
