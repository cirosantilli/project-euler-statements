import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p85.py.ast»
import ProjectEulerSolutions.Lib.RectangleApproximation
import lang.py.FormalSW.HeapCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p85
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.RectangleApproximation
open ProjectEulerSolutions.TriPentHex (triangular)
set_option Elab.async false

abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)

private theorem triangular_evaluate (module : Module) (env : HeapCalls.Env) (name : String)
    (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (found : env name = some (number n)) :
    Evaluates module env (.binOp
      (.binOp (.name name) .mult (.binOp (.name name) .add (.constant (.int 1))))
      .floorDiv (.constant (.int 2))) heap (number (triangular n)) heap globals := by
  apply Evaluates.binary (middle := heap) (afterRight := heap)
    (av := number (n * (n + 1))) (bv := number 2)
  · exact Evaluates.binary (av := number n) (bv := number (n + 1))
      (middle := heap) (afterRight := heap) (Evaluates.lookup found)
      (Evaluates.binary (value := number (n + 1)) (finalHeap := heap)
        (Evaluates.lookup found) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number]))
      (by simp [Mutable.binary, scalarBinary, number])
  · exact Evaluates.constant
  · simp [Mutable.binary, scalarBinary, number, triangular, Int.natCast_ediv]

theorem rect_count.result (m n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue P85Ast.module "rect_count" [number m, number n] heap
      (number (count m n)) heap globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (middle := heap) (afterRight := heap)
    (av := number (triangular m)) (bv := number (triangular n))
  · exact triangular_evaluate _ _ "m" m heap globals (by cases globals <;> rfl)
  · exact triangular_evaluate _ _ "n" n heap globals (by cases globals <;> rfl)
  · simp [Mutable.binary, scalarBinary, number, count]

end data.«project-euler-statements».data.py.project_euler_statements.p85
