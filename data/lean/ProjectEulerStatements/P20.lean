import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic

namespace ProjectEulerStatements.P20

def digitSum (n : Nat) : Nat :=
  (Nat.digits 10 n).sum

def naive (n : Nat) : Nat :=
  digitSum (Nat.factorial n)

example : naive 10 = 27 := by
  native_decide

end ProjectEulerStatements.P20
