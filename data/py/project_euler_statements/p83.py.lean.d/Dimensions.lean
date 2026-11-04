import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».Bound
import ProjectEulerSolutions.Lib.TriangleBufferCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RectangularMatrixCalls
open ProjectEulerSolutions.TriangleBufferCalls (number)
set_option Elab.async false

theorem dims.result (heap : Mutable.Heap) (address : Nat) (rows : MatrixRows)
    (found : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2))) :
    ReturnsValue program "dims" [.ref address] heap (.ref heap.length)
      (heap ++ [.tuple [number rows.length, number ((rows.map Prod.snd).headD []).length]]) := by
  let entry := argumentEnv arguments [.ref address]
  have height : Evaluates program entry (.builtinCall .len [.name "matrix"])
      heap (number rows.length) heap := by
    apply Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil)
    simp [HeapCalls.primitive, Mutable.length, found]
  have width : Evaluates program entry
      (.ifExp (.name "matrix") (.builtinCall .len [.subscript (.name "matrix") (.constant (.int 0))])
        (.constant (.int 0))) heap (number ((rows.map Prod.snd).headD []).length) heap := by
    cases rows with
    | nil =>
        exact Evaluates.conditional (flag := false) (Evaluates.lookup rfl)
          (by simp [Mutable.truth, found]) Evaluates.constant
    | cons first rest =>
        apply Evaluates.conditional (flag := true) (Evaluates.lookup rfl)
          (by simp [Mutable.truth, found])
        have row : Evaluates program entry (.subscript (.name "matrix") (.constant (.int 0)))
            heap (.ref first.1) heap := by
          apply Evaluates.subscript (by intros a b c impossible; cases impossible)
            (Evaluates.lookup rfl) Evaluates.constant
          simp [Mutable.getItem, found, Mutable.index, Except.map]
        apply Evaluates.builtin (.cons row .nil)
        simp [HeapCalls.primitive, Mutable.length, reads first (by simp), encode]
  apply BlockReturns.function (args := arguments) rfl rfl
  exact BlockReturns.return_value (Evaluates.tuple (.cons height (.cons width .nil)) (by simp))

end data.«project-euler-statements».data.py.project_euler_statements.p83
