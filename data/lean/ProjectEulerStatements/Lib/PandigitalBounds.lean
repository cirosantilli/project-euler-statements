import ProjectEulerStatements.P32
import Mathlib.Data.Nat.Digits.Lemmas
import Lean.Elab.Tactic.Omega

/-! Decimal-length bounds for the reference pandigital-product search.

The nine-digit requirement alone reduces the reference rectangle to the two
factor-length cases used by the optimized solver. No digit-mask property or
computed search result is needed for this reduction. -/
namespace ProjectEulerStatements.PandigitalBounds

set_option Elab.async false

theorem pandigital_length (a b : Nat) (accepted : P32.pandigitalProduct a b = true) :
    (Nat.digits 10 a).length + (Nat.digits 10 b).length +
      (Nat.digits 10 (a * b)).length = 9 := by
  simp only [P32.pandigitalProduct, P32.isPandigital1to9, Bool.and_eq_true,
    decide_eq_true_eq] at accepted
  simpa only [List.length_append, P32.digitsBE, List.length_reverse] using accepted.1.1

private theorem length_le (n k : Nat) (bounded : n < 10 ^ k) :
    (Nat.digits 10 n).length ≤ k :=
  (Nat.digits_length_le_iff (b := 10) (k := k) (by decide) n).mpr bounded

private theorem length_gt (n k : Nat) (bounded : 10 ^ k ≤ n) :
    k < (Nat.digits 10 n).length :=
  (Nat.lt_digits_length_iff (b := 10) (k := k) (by decide) n).mpr bounded

/-- The default reference domain contains only one-by-four or two-by-three
digit identities, and their products always have four decimal digits. -/
theorem reference_bounds (a b : Nat)
    (aPositive : 1 ≤ a) (aBounded : a ≤ 99)
    (_bPositive : 1 ≤ b) (bBounded : b ≤ 9999)
    (accepted : P32.pandigitalProduct a b = true) :
    (1000 ≤ a * b ∧ a * b ≤ 9999) ∧
      (if a < 10 then 1000 ≤ b ∧ b ≤ 9999 else 100 ≤ b ∧ b ≤ 999) := by
  have total := pandigital_length a b accepted
  have aLengthPositive := length_gt a 0 aPositive
  have aLengthBounded := length_le a 2 (by omega)
  have bLengthBounded := length_le b 4 (by omega)
  have productLength : (Nat.digits 10 (a * b)).length = 4 ∧
      (if a < 10 then 1000 ≤ b ∧ b ≤ 9999 else 100 ≤ b ∧ b ≤ 999) := by
    by_cases oneDigit : a < 10
    · have aLength := length_le a 1 oneDigit
      have bLower : 1000 ≤ b := by
        by_contra missing
        have bLength := length_le b 3 (by omega)
        have productBound := Nat.mul_le_mul (show a ≤ 9 by omega) (show b ≤ 999 by omega)
        have productLength := length_le (a * b) 4 (by omega)
        omega
      have bLength := length_gt b 3 bLower
      exact ⟨by omega, by simp only [if_pos oneDigit]; exact ⟨bLower, bBounded⟩⟩
    · have aLength := length_gt a 1 (by omega)
      have bLower : 100 ≤ b := by
        by_contra missing
        have bLength := length_le b 2 (by omega)
        have productBound := Nat.mul_le_mul aBounded (show b ≤ 99 by omega)
        have productLength := length_le (a * b) 4 (by omega)
        omega
      have bUpper : b ≤ 999 := by
        by_contra missing
        have bLength := length_gt b 3 (by omega)
        have productBound := Nat.mul_le_mul (show 10 ≤ a by omega) (show 1000 ≤ b by omega)
        have productLength := length_gt (a * b) 4 productBound
        omega
      have bLengthLower := length_gt b 2 bLower
      have bLengthUpper := length_le b 3 (by omega)
      exact ⟨by omega, by simp only [if_neg oneDigit]; exact ⟨bLower, bUpper⟩⟩
  refine ⟨⟨?_, ?_⟩, productLength.2⟩
  · exact (Nat.lt_digits_length_iff (b := 10) (k := 3) (by decide) (a * b)).mp
      (by omega)
  · have upper := (Nat.digits_length_le_iff (b := 10) (k := 4) (by decide) (a * b)).mp
        (by omega)
    omega

end ProjectEulerStatements.PandigitalBounds
