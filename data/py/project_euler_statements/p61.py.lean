import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p61.py.ast»
import FormalSW
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace data.«project-euler-statements».data.py.project_euler_statements.p61.polygonal
open FormalSW.PyAst

def answer (sides index : Int) : Int :=
  index * ((sides - 2) * index - (sides - 4)) / 2

/-- The actual arithmetic source returns on every pair of signed integers. -/
theorem result (sides index : Int) :
    Finishes (scalarFunction P61Ast.module "polygonal" [.int sides, .int index]).step
      (scalarFunction P61Ast.module "polygonal" [.int sides, .int index]).initial
      (.ok (.int (answer sides index))) := by
  apply Execution.finishes_of_observe (fuel := 1)
  rfl

theorem «Returns» (sides index : Int) :
    (scalarFunction P61Ast.module "polygonal" [.int sides, .int index]).Returns :=
  ⟨.int (answer sides index), result sides index⟩

theorem «Supported» (sides index : Int) :
    (scalarFunction P61Ast.module "polygonal" [.int sides, .int index]).Supported :=
  («Returns» sides index).supported

/-- The exact recurrence retains signed floor-division semantics. -/
theorem step (s n : Int) : answer s (n + 1) = answer s n + (s - 2) * n + 1 := by
  unfold answer
  have numerator : (n + 1) * ((s - 2) * (n + 1) - (s - 4)) =
      n * ((s - 2) * n - (s - 4)) + ((s - 2) * n + 1) * 2 := by ring
  rw [numerator, Int.add_mul_ediv_right _ _ (by decide : (2 : Int) ≠ 0)]
  ring

theorem increasing_step (s n : Int) (sides : 3 ≤ s) (positive : 1 ≤ n) :
    answer s n < answer s (n + 1) := by
  rw [step]
  have product : 0 ≤ (s - 2) * n := mul_nonneg (by omega) (by omega)
  omega

/-- The finite reference window contains every four-digit value of all six families. -/
theorem above_four_digits (s n : Int) (sides : 3 ≤ s) (large : 141 ≤ n) :
    10000 ≤ answer s n := by
  have extra : 0 ≤ (s - 3) * (n * (n - 1)) :=
    mul_nonneg (by omega) (mul_nonneg (by omega) (by omega))
  have triangle : (20000 : Int) ≤ n * (n + 1) := by
    nlinarith [sq_nonneg (n - 141)]
  have numerator : (20000 : Int) ≤ n * ((s - 2) * n - (s - 4)) := by
    nlinarith [extra]
  unfold answer
  omega

end data.«project-euler-statements».data.py.project_euler_statements.p61.polygonal
