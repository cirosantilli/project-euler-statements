import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Totient
import Lean.Elab.Tactic.Omega

/-! Decimal digit permutations and the necessary filters in the totient-ratio scan. -/
namespace ProjectEulerStatements.TotientPermutation
set_option Elab.async false

def digitsSorted (n : Nat) : List Nat :=
  (Nat.digits 10 n).mergeSort (fun a b => decide (a ≤ b))

def isPermutation (a b : Nat) : Bool := decide (digitsSorted a = digitsSorted b)

/-- Sorting equality expresses exactly a permutation of the positional digits. -/
theorem permutation_iff (a b : Nat) :
    isPermutation a b = true ↔ (Nat.digits 10 a).Perm (Nat.digits 10 b) := by
  simp only [isPermutation, decide_eq_true_eq]
  constructor
  · intro same
    exact (List.mergeSort_perm _ _).symm.trans
      ((by rw [same] : (digitsSorted a).Perm (digitsSorted b)).trans (List.mergeSort_perm _ _))
  · intro same
    exact List.Perm.eq_of_pairwise (fun _ _ _ _ lower upper => le_antisymm lower upper)
      (List.pairwise_mergeSort' (· ≤ ·) _) (List.pairwise_mergeSort' (· ≤ ·) _)
      ((List.mergeSort_perm _ _).trans (same.trans (List.mergeSort_perm _ _).symm))

/-- Congruence modulo nine is determined by the decimal digit sum. -/
theorem digit_sum_mod (n : Nat) : n % 9 = (Nat.digits 10 n).sum % 9 := by
  calc
    n % 9 = Nat.ofDigits 10 (Nat.digits 10 n) % 9 := by rw [Nat.ofDigits_digits]
    _ = Nat.ofDigits (10 % 9) (Nat.digits 10 n) % 9 := Nat.ofDigits_mod _ _ _
    _ = (Nat.digits 10 n).sum % 9 := by simp [Nat.ofDigits_one]

theorem permutation_mod (a b : Nat) (same : isPermutation a b = true) : a % 9 = b % 9 := by
  calc
    a % 9 = (Nat.digits 10 a).sum % 9 := digit_sum_mod a
    _ = (Nat.digits 10 b).sum % 9 :=
      congrArg (fun n => n % 9) ((permutation_iff a b).mp same).sum_eq
    _ = b % 9 := (digit_sum_mod b).symm

/-- Permuting positive digits preserves the moving decimal-width interval. -/
theorem permutation_width (a b width : Nat) (same : isPermutation a b = true)
    (lower : 10 ^ width ≤ a) (upper : a < 10 ^ (width + 1)) :
    10 ^ width ≤ b ∧ b < 10 ^ (width + 1) := by
  have length := ((permutation_iff a b).mp same).length_eq
  have above := (Nat.lt_digits_length_iff (b := 10) (k := width) (by decide) a).mpr lower
  have below := (Nat.digits_length_le_iff (b := 10) (k := width + 1) (by decide) a).mpr upper
  rw [length] at above below
  exact ⟨(Nat.lt_digits_length_iff (by decide) b).mp above,
    (Nat.digits_length_le_iff (by decide) b).mp below⟩

/-- The signed subtraction in Python has the same necessary mod-nine test. -/
theorem permutation_difference (a b : Nat) (same : isPermutation a b = true) :
    ((a : Int) - b) % 9 = 0 := by
  have congruent := permutation_mod a b same
  omega

/-- Both inexpensive filters preserve every eligible totient permutation. -/
theorem filters (n width : Nat) (same : isPermutation n n.totient = true)
    (lower : 10 ^ width ≤ n) (upper : n < 10 ^ (width + 1)) :
    10 ^ width ≤ n.totient ∧ n.totient < 10 ^ (width + 1) ∧
      ((n : Int) - n.totient) % 9 = 0 :=
  ⟨(permutation_width n n.totient width same lower upper).1,
    (permutation_width n n.totient width same lower upper).2,
    permutation_difference n n.totient same⟩

end ProjectEulerStatements.TotientPermutation
