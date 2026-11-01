import Mathlib.Combinatorics.Enumerative.Pentagonal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Executable pentagonal contributions and finite loop tails, independent of generating series. -/
namespace ProjectEulerStatements.PartitionPentagonalLoop
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

theorem first_ge_index (k : Nat) : k ≤ first k := by
  by_cases zero : k = 0
  · subst k
    simp [first, pentagonal]
  · have quadratic := two_mul_natCast_pentagonal (k : Int)
    have product : 0 ≤ (k : Int)*(k-1) := mul_nonneg (by omega) (by omega)
    have bound : (k : Int) ≤ (first k : Int) := by
      change (k : Int) ≤ (pentagonal (k : Int) : Int)
      nlinarith
    omega

theorem first_positive (k : Nat) (positive : 0 < k) : 0 < first k := by
  have lower := first_ge_index k
  omega

theorem second_gt (k : Nat) (positive : 0 < k) : first k < second k :=
  pentagonal_lt_pentagonal_neg (by omega)

theorem first_monotone {j k : Nat} (ordered : j ≤ k) : first j ≤ first k := by
  by_cases same : j = k
  · subst k
    rfl
  · exact le_of_lt (pentagonal_strictMonoOn (by simp) (by simp) (by omega))

theorem piece_outside (values : Nat → Int) (n k : Nat) (positive : 0 < k)
    (outside : n < first k) : piece values n k = 0 := by
  have later := second_gt k positive
  simp [piece, show ¬ first k ≤ n by omega, show ¬ second k ≤ n by omega]

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

end ProjectEulerStatements.PartitionPentagonalLoop
