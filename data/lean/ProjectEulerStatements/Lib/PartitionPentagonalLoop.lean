import ProjectEulerStatements.Lib.PartitionRecurrence
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.ModEq

/-! Paired pentagonal contributions, their complete finite sums, and modular invariance. -/
namespace ProjectEulerStatements.PartitionPentagonalLoop
open PartitionRecurrence
open scoped BigOperators
set_option Elab.async false

def first (k : Nat) : Nat := pentagonal (k : Int)
def second (k : Nat) : Nat := pentagonal (-(k : Int))
def sign (k : Int) : Int := if k % 2 = 1 then 1 else -1

def piece (values : Nat → Int) (n k : Nat) : Int :=
  sign k * (if first k ≤ n then values (n-first k) else 0) +
    sign k * (if second k ≤ n then values (n-second k) else 0)

theorem first_cast (k : Nat) : (first k : Int) = (k : Int)*(3*k-1)/2 :=
  natCast_pentagonal k

theorem second_cast (k : Nat) : (second k : Int) = (k : Int)*(3*k+1)/2 := by
  rw [second, natCast_pentagonal]
  congr 1
  ring

theorem first_positive (k : Nat) (positive : 0 < k) : 0 < first k := by
  have lower := (PartitionPentagonal.index_bounds (k : Int)).2
  change (k : Int) ≤ (first k : Int) at lower
  omega

theorem second_gt (k : Nat) (positive : 0 < k) : first k < second k :=
  pentagonal_lt_pentagonal_neg (by omega)

theorem first_ge_index (k : Nat) : k ≤ first k := by
  have lower := (PartitionPentagonal.index_bounds (k : Int)).2
  change (k : Int) ≤ (first k : Int) at lower
  omega

theorem first_monotone {j k : Nat} (ordered : j ≤ k) : first j ≤ first k := by
  by_cases same : j = k
  · subst k
    rfl
  · exact le_of_lt (pentagonal_strictMonoOn (by simp) (by simp) (by omega))

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

theorem piece_outside (values : Nat → Int) (n k : Nat) (positive : 0 < k)
    (outside : n < first k) : piece values n k = 0 := by
  have later := second_gt k positive
  simp [piece, show ¬ first k ≤ n by omega, show ¬ second k ≤ n by omega]

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

def tail (values : Nat → Int) (n k : Nat) : Int :=
  ∑ j ∈ Finset.Ico k (n+1), piece values n j

theorem tail_step (values : Nat → Int) (n k : Nat) (inside : k ≤ n) :
    tail values n k = piece values n k + tail values n (k+1) :=
  Finset.sum_eq_sum_Ico_succ_bot (by omega) _

/-- The actual pentagonal break condition makes every remaining summand vanish. -/
theorem tail_done (values : Nat → Int) (n k : Nat) (positive : 0 < k)
    (outside : n < first k) : tail values n k = 0 := by
  apply Finset.sum_eq_zero
  intro j member
  have ordered : k ≤ j := (Finset.mem_Ico.mp member).1
  have larger := first_monotone ordered
  exact piece_outside values n j (by omega) (by omega)

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
