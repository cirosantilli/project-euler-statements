import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P52

def digitsSorted (n : Nat) : List Nat :=
  (Nat.digits 10 n).mergeSort (fun a b => decide (a ≤ b))

/-- Two numbers have the same multiset of decimal digits. -/
def sameDigits (a b : Nat) : Bool :=
  digitsSorted a = digitsSorted b

/-- Whether `x` has permuted multiples up to `6x`. -/
def hasPermutedMultiples (x : Nat) : Bool :=
  (List.range 5).all (fun i => sameDigits x ((i + 2) * x))

/-- Existence of a number with permuted multiples up to `6x`. -/
theorem exists_permuted_multiples : ∃ x, hasPermutedMultiples x = true := by
  sorry

/-- Smallest positive integer `x` such that `2x..6x` are digit permutations of `x`. -/
def naive : Nat :=
  Nat.find exists_permuted_multiples

example : sameDigits 125874 (2 * 125874) = true := by
  native_decide

end ProjectEulerStatements.P52
