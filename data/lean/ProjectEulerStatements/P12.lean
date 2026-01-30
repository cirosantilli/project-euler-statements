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

def firstTriangleOver (k : Nat) (h : ∃ n, divisorCount (triangle n) > k) : Nat :=
  triangle (Nat.find h)

def naive (k : Nat) (h : ∃ n, divisorCount (triangle n) > k) : Nat :=
  firstTriangleOver k h

theorem exists_triangle_divisorCount_gt (k : Nat) : ∃ n, divisorCount (triangle n) > k := by
  -- Sketch: use unboundedness of divisorCount on coprime products.
  -- Choose n even with n/2 having many divisors, and use coprimeness of n/2 and n+1.
  -- Then divisorCount (triangle n) = divisorCount (n/2) * divisorCount (n+1) is unbounded.
  -- Formalizing this likely needs lemmas about divisorCount multiplicativity on coprime inputs.
  sorry

example : triangle 7 = 28 := by
  native_decide

example : firstTriangleOver 5 ⟨7, by native_decide⟩ = 28 := by
  native_decide

end ProjectEulerStatements.P12
