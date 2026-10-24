import ProjectEulerStatements.Lib.SqrtPeriodicity
import Mathlib.Data.Nat.Sqrt

/-! Natural square-root inputs and computable period lengths with no execution budget. -/
namespace ProjectEulerStatements.SqrtReducedStates
set_option Elab.async false

theorem sqrt_bounds (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    Bounds (n : Int) (Nat.sqrt n : Int) := by
  have below : Nat.sqrt n * Nat.sqrt n < n := lt_of_le_of_ne (Nat.sqrt_le n) nonsquare
  have above := Nat.lt_succ_sqrt n
  refine ⟨by omega, ?_, ?_⟩
  · exact_mod_cast (show Nat.sqrt n ^ 2 < n by simpa only [pow_two] using below)
  · exact_mod_cast
      (show n < (Nat.sqrt n + 1) ^ 2 by simpa only [pow_two, Nat.succ_eq_add_one] using above)

def length (n : Nat) : Nat :=
  if square : Nat.sqrt n * Nat.sqrt n = n then 0 else period (sqrt_bounds n square)

def trajectory (n index : Nat) : State := (step n (Nat.sqrt n))^[index] (0, 1)

theorem trajectory_step (n index : Nat) :
    step n (Nat.sqrt n) (trajectory n index) = trajectory n (index + 1) :=
  (Function.iterate_succ_apply' (step n (Nat.sqrt n)) index (0, 1)).symm

theorem trajectory_succ (n index : Nat) :
    trajectory n (index + 1) = (step n (Nat.sqrt n))^[index] (first n (Nat.sqrt n)) := by
  rw [trajectory, Function.iterate_succ_apply, step_initial]

theorem trajectory_reduced (n index : Nat) (positive : 0 < index)
    (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    Reduced n (Nat.sqrt n) (trajectory n index) := by
  cases index with
  | zero => omega
  | succ index =>
      rw [trajectory_succ]
      exact orbit_reduced (sqrt_bounds n nonsquare) index

theorem trajectory_denominator_positive (n index : Nat)
    (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) : 0 < (trajectory n index).2 := by
  cases index with
  | zero => change (0 : Int) < 1; omega
  | succ index =>
      rw [trajectory_succ]
      exact (orbit_reduced (sqrt_bounds n nonsquare) index).2.2.1

theorem length_of_square (n : Nat) (square : Nat.sqrt n * Nat.sqrt n = n) : length n = 0 := by
  simp only [length, dif_pos square]

theorem length_of_nonsquare (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    length n = period (sqrt_bounds n nonsquare) := by
  simp only [length, dif_neg nonsquare]

theorem length_positive (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) : 0 < length n := by
  rw [length_of_nonsquare n nonsquare]
  exact period_positive _

theorem source_stops (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    coefficient (Nat.sqrt n) ((step n (Nat.sqrt n))^[length n - 1] (first n (Nat.sqrt n))) =
      2 * Nat.sqrt n := by
  rw [length_of_nonsquare n nonsquare, terminal_at_period]
  simp [coefficient, terminal, two_mul]

theorem source_continues (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (before : index + 1 < length n) :
    coefficient (Nat.sqrt n) ((step n (Nat.sqrt n))^[index] (first n (Nat.sqrt n))) ≠
      2 * Nat.sqrt n := by
  rw [length_of_nonsquare n nonsquare] at before
  intro same
  exact before_terminal (sqrt_bounds n nonsquare) index before
    ((coefficient_terminal_iff (sqrt_bounds n nonsquare)
      (orbit_reduced (sqrt_bounds n nonsquare) index)).mp same)

theorem trajectory_noninitial (n index : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (positive : 0 < index) : trajectory n index ≠ trajectory n 0 := by
  intro same
  have valid := trajectory_reduced n index positive nonsquare
  rw [same] at valid
  have lower := valid.2.2.2.1
  change (Nat.sqrt n : Int) - 0 < 1 at lower
  have positiveRoot := (sqrt_bounds n nonsquare).root_positive
  omega

/-- Before the first repeated state, the reference's recorded states are all distinct. -/
theorem trajectory_injective (n left right : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n)
    (leftBefore : left ≤ length n) (rightBefore : right ≤ length n)
    (same : trajectory n left = trajectory n right) : left = right := by
  cases left with
  | zero =>
      by_contra different
      exact trajectory_noninitial n right nonsquare (by omega) same.symm
  | succ left =>
      cases right with
      | zero => exact False.elim (trajectory_noninitial n (left + 1) nonsquare (by omega) same)
      | succ right =>
          rw [trajectory_succ, trajectory_succ] at same
          have equal := orbit_injective (sqrt_bounds n nonsquare) left right
            (by rw [← length_of_nonsquare n nonsquare]; omega)
            (by rw [← length_of_nonsquare n nonsquare]; omega) same
          omega

theorem trajectory_first_repeat (n : Nat) (nonsquare : Nat.sqrt n * Nat.sqrt n ≠ n) :
    trajectory n (length n + 1) = trajectory n 1 := by
  rw [trajectory_succ, length_of_nonsquare n nonsquare, period_returns]
  exact (trajectory_succ n 0).symm

end ProjectEulerStatements.SqrtReducedStates
