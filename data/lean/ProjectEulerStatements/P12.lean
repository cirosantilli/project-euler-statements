import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat

namespace ProjectEulerStatements.P12

def triangle (n : Nat) : Nat :=
  n * (n + 1) / 2

def divisors (n : Nat) : Finset Nat :=
  (Finset.Icc 1 n).filter (fun d => d ∣ n)

def divisorCount (n : Nat) : Nat :=
  (divisors n).card

def firstTriangleOver (k limit : Nat) : Nat :=
  match (List.find? (fun n => divisorCount (triangle n) > k) (List.range (limit + 1))) with
  | some n => triangle n
  | none => 0

def naive (k limit : Nat) : Nat :=
  firstTriangleOver k limit

example : triangle 7 = 28 := by
  native_decide

example : firstTriangleOver 5 7 = 28 := by
  native_decide

end ProjectEulerStatements.P12
