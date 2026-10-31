import ProjectEulerStatements.Lib.PartitionPentagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-! An integer pentagonal recurrence with paired positive and negative indices. -/
namespace ProjectEulerStatements.PartitionRecurrence
open scoped BigOperators
set_option Elab.async false

def count (n : Nat) : Int := P76.countWays n n

def term (n : Nat) (k : Int) : Int :=
  if pentagonal k ≤ n then
    if Even k then count (n-pentagonal k) else -count (n-pentagonal k)
  else 0

theorem cast_term (n : Nat) (k : Int) : (term n k : ℚ) = PartitionPentagonal.term n k := by
  unfold term PartitionPentagonal.term count
  split_ifs <;> simp

theorem convolution (n : Nat) :
    (∑ k ∈ Finset.Icc (-((2*n : Nat) : Int)) (2*n), term n k) =
      if n = 0 then 1 else 0 := by
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_sum, cast_term, Int.cast_ite, Int.cast_one, Int.cast_zero] using
    PartitionPentagonal.convolution n

theorem term_outside (n : Nat) (k : Int) (outside : k < -(n : Int) ∨ (n : Int) < k) :
    term n k = 0 := by
  obtain ⟨lower, upper⟩ := PartitionPentagonal.index_bounds k
  have large : ¬ pentagonal k ≤ n := by omega
  simp only [term, if_neg large]

theorem convolution_trimmed (n : Nat) :
    (∑ k ∈ Finset.Icc (-(n : Int)) n, term n k) = if n = 0 then 1 else 0 := by
  rw [← convolution n]
  apply Finset.sum_subset
  · intro k member
    simp only [Finset.mem_Icc] at member ⊢
    omega
  · intro k _ outside
    apply term_outside
    simp only [Finset.mem_Icc, not_and_or, not_le] at outside
    exact outside

/-- Splitting a symmetric integer interval pairs each positive index with its negative. -/
theorem sum_pairs (f : Int → Int) (n : Nat) :
    (∑ k ∈ Finset.Icc (-(n : Int)) n, f k) =
      f 0 + ∑ j ∈ Finset.range n, (f (j+1) + f (-(j+1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, Finset.sum_Icc_succ_eq_add_endpoints, ih,
        Finset.sum_range_succ]
      ring

theorem term_zero (n : Nat) : term n 0 = count n := by simp [term, pentagonal]

/-- The partition value is the negative of all nonzero signed pentagonal contributions. -/
theorem recurrence (n : Nat) (positive : 0 < n) :
    count n = -∑ j ∈ Finset.range n, (term n (j+1) + term n (-(j+1))) := by
  have identity := convolution_trimmed n
  rw [sum_pairs, term_zero, if_neg (by omega : n ≠ 0)] at identity
  omega

end ProjectEulerStatements.PartitionRecurrence
