import ProjectEulerStatements.Lib.PartitionRecurrence
import ProjectEulerStatements.Lib.PartitionPentagonalTerms
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.ModEq

/-! Paired pentagonal contributions, their complete finite sums, and modular invariance. -/
namespace ProjectEulerStatements.PartitionPentagonalLoop
open PartitionRecurrence
open scoped BigOperators
set_option Elab.async false

theorem piece_eq_terms (n k : Nat) :
    piece count n k = -(term n k + term n (-(k : Int))) := by
  by_cases even : Even (k : Int)
  · have notOdd : ¬ (k : Int) % 2 = 1 := by
      have := Int.even_iff.mp even
      omega
    simp [piece, sign, term, first, second, even, notOdd, mul_ite]
    split_ifs <;> ring
  · have odd : (k : Int) % 2 = 1 := Int.not_even_iff.mp even
    simp [piece, sign, term, first, second, even, odd]
    split_ifs <;> ring

theorem recurrence (n : Nat) (positive : 0 < n) :
    count n = ∑ j ∈ Finset.range n, piece count n (j+1) := by
  rw [PartitionRecurrence.recurrence n positive, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j member
  exact (piece_eq_terms n (j+1)).symm

/-- Replacing table entries by any congruent representatives preserves each paired contribution. -/
theorem piece_mod (values : Nat → Int) (n k : Nat) (modulus : Int)
    (same : ∀ j < n, values j % modulus = count j % modulus) (positive : 0 < k) :
    piece values n k % modulus = piece count n k % modulus := by
  have firstPos := first_positive k positive
  have secondPos : 0 < second k := by have := second_gt k positive; omega
  have one : (if first k ≤ n then values (n-first k) else 0) % modulus =
      (if first k ≤ n then count (n-first k) else 0) % modulus := by
    split_ifs
    · exact same _ (by omega)
    · rfl
  have two : (if second k ≤ n then values (n-second k) else 0) % modulus =
      (if second k ≤ n then count (n-second k) else 0) % modulus := by
    split_ifs
    · exact same _ (by omega)
    · rfl
  exact (Int.ModEq.mul_left (sign k) one).add (Int.ModEq.mul_left (sign k) two)

theorem tail_start (n : Nat) (positive : 0 < n) : tail count n 1 = count n := by
  rw [recurrence n positive, tail, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

theorem tail_mod (values : Nat → Int) (n k : Nat) (modulus : Int)
    (same : ∀ j < n, values j % modulus = count j % modulus) (positive : 0 < k) :
    tail values n k % modulus = tail count n k % modulus := by
  unfold tail
  apply Int.ModEq.sum
  intro j member
  have ordered : k ≤ j := (Finset.mem_Ico.mp member).1
  exact piece_mod values n j modulus same (by omega)

/-- A complete loop over congruent previous entries computes the next partition residue. -/
theorem tail_start_mod (values : Nat → Int) (n : Nat) (modulus : Int)
    (same : ∀ j < n, values j % modulus = count j % modulus) (positive : 0 < n) :
    tail values n 1 % modulus = count n % modulus := by
  rw [tail_mod values n 1 modulus same (by omega), tail_start n positive]

end ProjectEulerStatements.PartitionPentagonalLoop
