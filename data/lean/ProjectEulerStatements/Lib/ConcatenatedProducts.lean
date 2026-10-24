import ProjectEulerStatements.P38
import ProjectEulerStatements.Lib.DecimalDigits
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Range

/-! Decimal concatenation and its strictly increasing length for positive factors. -/
namespace ProjectEulerStatements.ConcatenatedProducts

open P38

theorem concatProduct_zero (n : Nat) : concatProduct n 0 = 0 := rfl

theorem concatProduct_succ (n k : Nat) :
    concatProduct n (k + 1) = concatNat (concatProduct n k) (n * (k + 1)) := by
  simp [concatProduct, List.range_succ, List.foldl_append]

theorem digitsBE_concat (a b : Nat) :
    digitsBE (concatNat a b) = digitsBE a ++ digitsBE b := by
  have joined := Nat.digits_append_digits (b := 10) (m := a) (n := b) (by decide)
  have ordered : b + 10 ^ (Nat.digits 10 b).length * a = concatNat a b := by
    simp [concatNat, numDigits, Nat.mul_comm, Nat.add_comm]
  rw [ordered] at joined
  simpa only [digitsBE, List.reverse_append] using congrArg List.reverse joined.symm

theorem numDigits_concat (a b : Nat) :
    numDigits (concatNat a b) = numDigits a + numDigits b := by
  have lengths := congrArg List.length (digitsBE_concat a b)
  simpa only [digitsBE, numDigits, List.length_reverse, List.length_append] using lengths

theorem numDigits_positive (n : Nat) (positive : 0 < n) : 0 < numDigits n := by
  simp only [numDigits, List.length_pos_iff_ne_nil]
  exact Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)

theorem concatProduct_digits_succ (n k : Nat) :
    digitsBE (concatProduct n (k + 1)) =
      digitsBE (concatProduct n k) ++ digitsBE (n * (k + 1)) := by
  rw [concatProduct_succ, digitsBE_concat]

theorem concatProduct_length_succ (n k : Nat) :
    numDigits (concatProduct n (k + 1)) =
      numDigits (concatProduct n k) + numDigits (n * (k + 1)) := by
  rw [concatProduct_succ, numDigits_concat]

theorem concatProduct_length_strict (n : Nat) (positive : 0 < n) :
    StrictMono (fun k => numDigits (concatProduct n k)) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [concatProduct_length_succ]
  have := numDigits_positive (n * (k + 1)) (Nat.mul_pos positive (by omega))
  omega

theorem concatProduct_length_lower (n k : Nat) (positive : 0 < n) :
    k ≤ numDigits (concatProduct n k) := by
  induction k with
  | zero => omega
  | succ k ih =>
      have step := concatProduct_length_strict n positive (Nat.lt_succ_self k)
      dsimp only at step
      simp only [Nat.succ_eq_add_one] at step ⊢
      omega

theorem nine_reached (n : Nat) (positive : 0 < n) :
    ∃ k, 9 ≤ numDigits (concatProduct n k) :=
  ⟨9, concatProduct_length_lower n 9 positive⟩

/-- The first product count whose decimal concatenation has at least nine digits. -/
noncomputable def stopCount (n : Nat) : Nat :=
  if positive : 0 < n then Nat.find (nine_reached n positive) else 0

theorem stopCount_spec (n : Nat) (positive : 0 < n) :
    9 ≤ numDigits (concatProduct n (stopCount n)) := by
  simpa only [stopCount, dif_pos positive] using Nat.find_spec (nine_reached n positive)

theorem before_stopCount (n k : Nat) (positive : 0 < n) (before : k < stopCount n) :
    numDigits (concatProduct n k) < 9 := by
  simp only [stopCount, dif_pos positive] at before
  have := Nat.find_min (nine_reached n positive) before
  omega

theorem stopCount_bounds (n : Nat) (positive : 0 < n) :
    1 ≤ stopCount n ∧ stopCount n ≤ 9 := by
  have reached := stopCount_spec n positive
  have lower : 0 < stopCount n := by
    by_contra h
    have zero : stopCount n = 0 := by omega
    simp [zero, concatProduct_zero, numDigits] at reached
  have upper : stopCount n ≤ 9 := by
    by_contra h
    have := before_stopCount n 9 positive (by omega)
    have := concatProduct_length_lower n 9 positive
    omega
  omega

theorem nine_digits_unique (n k : Nat) (positive : 0 < n)
    (nine : numDigits (concatProduct n k) = 9) : k = stopCount n := by
  have reached := stopCount_spec n positive
  have strict := concatProduct_length_strict n positive
  rcases lt_trichotomy k (stopCount n) with before | equal | after
  · have := before_stopCount n k positive before
    omega
  · exact equal
  · have increasing := strict after
    dsimp only at increasing
    omega

theorem zero_product (k : Nat) : concatProduct 0 k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [concatProduct_succ, ih, concatNat, numDigits]

end ProjectEulerStatements.ConcatenatedProducts
