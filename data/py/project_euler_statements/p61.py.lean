import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p61.py.ast»
import FormalSW
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace data.«project-euler-statements».data.py.project_euler_statements.p61.polygonal
open FormalSW.PyAst

def answer (sides index : Int) : Int :=
  index * ((sides - 2) * index - (sides - 4)) / 2

def expression (sName nName : String) : Expr :=
  .binOp
    (.binOp (.name nName) .mult
      (.binOp (.binOp (.binOp (.name sName) .sub (.constant (.int 2))) .mult (.name nName))
        .sub (.binOp (.name sName) .sub (.constant (.int 4)))))
    .floorDiv (.constant (.int 2))

private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)

/-- Arithmetic evaluation leaves the caller heap and its global bindings untouched. -/
theorem expression_evaluates (sName nName : String) (s n : Int) (module : Module)
    (env : HeapCalls.Env) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (getS : env sName = some (number s)) (getN : env nName = some (number n)) :
    HeapCalls.Evaluates module env (expression sName nName) heap (number (answer s n)) heap globals := by
  apply HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (av := number (n * ((s - 2) * n - (s - 4)))) (bv := number 2)
  · apply HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (av := number n) (bv := number ((s - 2) * n - (s - 4)))
    · exact HeapCalls.Evaluates.lookup getN
    · apply HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (av := number ((s - 2) * n)) (bv := number (s - 4))
      · apply HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (av := number (s - 2)) (bv := number n)
        · exact HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (HeapCalls.Evaluates.lookup getS)
            HeapCalls.Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])
        · exact HeapCalls.Evaluates.lookup getN
        · simp [Mutable.binary, scalarBinary, number]
      · exact HeapCalls.Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap) (HeapCalls.Evaluates.lookup getS)
          HeapCalls.Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])
      · simp [Mutable.binary, scalarBinary, number]
    · simp [Mutable.binary, scalarBinary, number]
  · exact HeapCalls.Evaluates.constant
  · simp [Mutable.binary, scalarBinary, number, answer]

/-- The source helper can be called from a heap-based loop in any caller context. -/
theorem heap_result (s n : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    HeapCalls.ReturnsValue P61Ast.module "polygonal" [number s, number n] heap
      (number (answer s n)) heap globals := by
  let params := ((findFunctionIn P61Ast.module.body "polygonal").getD ([], [])).1
  let body := ((findFunctionIn P61Ast.module.body "polygonal").getD ([], [])).2
  let env := HeapCalls.functionEnv params body [number s, number n] globals
  apply HeapCalls.BlockReturns.function rfl rfl
  change HeapCalls.BlockReturns P61Ast.module env [.return (expression "sides" "index")] heap
    (number (answer s n)) heap globals
  apply HeapCalls.BlockReturns.return_value
  exact expression_evaluates _ _ _ _ _ _ _ _ (by cases globals <;> rfl) (by cases globals <;> rfl)

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
