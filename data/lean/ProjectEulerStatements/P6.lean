import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace ProjectEulerStatements.P6

open scoped BigOperators

def sumSquares (n : Nat) : Nat :=
  (Finset.Icc 1 n).sum (fun i => i ^ 2)

def squareSum (n : Nat) : Nat :=
  ((Finset.Icc 1 n).sum (fun i => i)) ^ 2

def naive (n : Nat) : Nat :=
  squareSum n - sumSquares n

example : sumSquares 10 = 385 := by
  native_decide

example : squareSum 10 = 3025 := by
  native_decide

example : naive 10 = 2640 := by
  native_decide

end ProjectEulerStatements.P6
