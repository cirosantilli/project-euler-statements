import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P10

open scoped BigOperators

def naive (n : Nat) : Nat :=
  ((Finset.range n).filter Nat.Prime).sum (fun p => p)

example : naive 10 = 17 := by
  native_decide

end ProjectEulerStatements.P10
