import ProjectEulerStatements.P76
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite Euler products invert the same bounded-part recurrence used by the Python reference. -/
namespace ProjectEulerStatements.PartitionGenerating
open scoped BigOperators PowerSeries
set_option Elab.async false

theorem countWays_stable (n max : Nat) (large : n ≤ max) :
    P76.countWays n max = P76.countWays n n := by
  induction max using Nat.strong_induction_on generalizing n with
  | h max smaller =>
      by_cases zero : n = 0
      · subst n
        simp
      · by_cases same : max = n
        · rw [same]
        · have positive : 0 < max := by omega
          rw [P76.countWays_step n max zero positive, if_neg (by omega : ¬ max ≤ n), Nat.zero_add]
          exact smaller (max-1) (by omega) n (by omega)

noncomputable section
variable {R : Type*} [CommRing R]

def bounded (max : Nat) : R⟦X⟧ := PowerSeries.mk (fun n => (P76.countWays n max : R))

@[simp] theorem coeff_bounded (max n : Nat) :
    PowerSeries.coeff n (bounded (R := R) max) = (P76.countWays n max : R) := by simp [bounded]

theorem bounded_zero : bounded (R := R) 0 = 1 := by
  apply PowerSeries.ext
  intro n
  simp [P76.countWays_no_parts, PowerSeries.coeff_one]

/-- Adding a permitted part multiplies the generating series by its geometric factor. -/
theorem bounded_step (max : Nat) :
    (1-(PowerSeries.X : R⟦X⟧)^(max+1)) * bounded (max+1) = bounded max := by
  apply PowerSeries.ext
  intro n
  simp only [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', coeff_bounded]
  by_cases zero : n = 0
  · subst n
    simp
  · rw [P76.countWays_step n (max+1) zero (by omega)]
    by_cases enough : max+1 ≤ n
    · simp only [if_pos enough, Nat.cast_add, Nat.add_sub_cancel]
      ring
    · simp only [if_neg enough, Nat.cast_add, Nat.cast_zero, Nat.add_sub_cancel]
      ring

def factors (max : Nat) : R⟦X⟧ := ∏ j ∈ Finset.range max, (1-PowerSeries.X^(j+1))

@[simp] theorem factors_zero : factors (R := R) 0 = 1 := by simp [factors]

theorem factors_succ (max : Nat) :
    factors (R := R) (max+1) = factors max * (1-PowerSeries.X^(max+1)) :=
  Finset.prod_range_succ _ _

/-- Every finite part set has an exact inverse Euler product. -/
theorem bounded_factors (max : Nat) : bounded (R := R) max * factors max = 1 := by
  induction max with
  | zero => simp [bounded_zero]
  | succ max ih =>
      rw [factors_succ]
      calc
        bounded (R := R) (max+1) * (factors max * (1-PowerSeries.X^(max+1))) =
            ((1-PowerSeries.X^(max+1)) * bounded (max+1)) * factors max := by ring
        _ = bounded (R := R) max * factors max := by rw [bounded_step]
        _ = 1 := ih

theorem coeff_bounded_stable (max n : Nat) (large : n ≤ max) :
    PowerSeries.coeff n (bounded (R := R) max) = (P76.countWays n n : R) := by
  rw [coeff_bounded, countWays_stable n max large]

end
end ProjectEulerStatements.PartitionGenerating
