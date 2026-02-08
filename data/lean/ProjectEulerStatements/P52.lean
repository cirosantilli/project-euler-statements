import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Find

namespace ProjectEulerStatements.P52

def digitsSorted (n : Nat) : List Nat :=
  (Nat.digits 10 n).mergeSort (fun a b => decide (a ≤ b))

/-- Two numbers have the same multiset of decimal digits. -/
def sameDigits (a b : Nat) : Bool :=
  digitsSorted a = digitsSorted b

/-- Whether `x` has permuted multiples up to `n*x` (for `n ≥ 2`). -/
def hasPermutedMultiples (n x : Nat) : Bool :=
  if n < 2 then
    false
  else
    (List.range (n - 1)).all (fun i => sameDigits x ((i + 2) * x))

/-- Existence of a number with permuted multiples up to `n*x`. -/
theorem exists_permuted_multiples (n : Nat) : ∃ x, hasPermutedMultiples n x = true := by
  sorry

/-- Smallest positive integer `x` such that `2x..n*x` are digit permutations of `x`. -/
noncomputable def naive (n : Nat) : Nat := by
  classical
  exact Nat.find (exists_permuted_multiples n)

example : sameDigits 125874 (2 * 125874) = true := by
  native_decide

end ProjectEulerStatements.P52
