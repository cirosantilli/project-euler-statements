import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».Read
import ProjectEulerSolutions.Lib.IntegerRangeCollection

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RectangularMatrixCalls
open ProjectEulerSolutions.TriangleBufferCalls (number working prefix_found)
open ProjectEulerStatements.P83 (getD2 bigVal)
set_option Elab.async false

abbrev initialTest : Expr := .boolOp .and
  [.compare (.name "r") [(.eq, .constant (.int 0))], .compare (.name "c") [(.eq, .constant (.int 0))]]
abbrev initialCell : Expr := .ifExp initialTest
  (.call (.name "get_d2") [.name "matrix", .constant (.int 0), .constant (.int 0)]) (.name "big")
abbrev initialRowExpression : Expr := .listComp initialCell [("c", .call (.name "range") [.name "cols"], [])]
def initialRow (matrix : List (List Int)) (row : Nat) : List Int :=
  (List.range (matrix.headD []).length).map (fun col => if row = 0 ∧ col = 0 then getD2 matrix 0 0 else bigVal matrix)

theorem initial_cell (heap : Mutable.Heap) (env : HeapCalls.Env) (address r c : Nat) (rows : MatrixRows)
    (found : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2)))
    (localMatrix : env "matrix" = some (.ref address)) (localRow : env "r" = some (number r))
    (localColumn : env "c" = some (number c)) (localBound : env "big" = some (number (bigVal (rows.map Prod.snd)))) :
    Evaluates program env initialCell heap
      (number (if r = 0 ∧ c = 0 then getD2 (rows.map Prod.snd) 0 0 else bigVal (rows.map Prod.snd))) heap := by
  have rowTest : Evaluates program env (.compare (.name "r") [(.eq, .constant (.int 0))]) heap
      (.scalar (.bool (decide (r = 0)))) heap := by
    apply Evaluates.compare (Evaluates.lookup localRow) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  have columnTest : Evaluates program env (.compare (.name "c") [(.eq, .constant (.int 0))]) heap
      (.scalar (.bool (decide (c = 0)))) heap := by
    apply Evaluates.compare (Evaluates.lookup localColumn) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  have tested : Evaluates program env initialTest heap (.scalar (.bool (decide (r = 0 ∧ c = 0)))) heap := by
    by_cases firstRow : r = 0
    · apply Evaluates.boolean_next (flag := true) (value := .scalar (.bool true))
        (by simpa only [firstRow, decide_true] using rowTest) rfl rfl
      simpa only [firstRow, true_and] using Evaluates.boolean_last columnTest rfl
    · simp only [firstRow, false_and, decide_false]
      exact Evaluates.boolean_stop (by simpa only [firstRow, decide_false] using rowTest) rfl rfl
  by_cases first : r = 0 ∧ c = 0
  · rw [if_pos first]
    apply Evaluates.conditional (flag := true) (by simpa only [first, and_self, decide_true] using tested) rfl
    exact Evaluates.call (.cons (Evaluates.lookup localMatrix) (.cons Evaluates.constant (.cons Evaluates.constant .nil)))
      (get_d2.result heap address rows 0 0 found reads)
  · rw [if_neg first]
    exact Evaluates.conditional (flag := false) (by simpa only [first, decide_false] using tested) rfl (Evaluates.lookup localBound)

theorem initial_row_allocation (heap : Mutable.Heap) (env : HeapCalls.Env) (address row : Nat) (rows : MatrixRows)
    (found : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2)))
    (localMatrix : env "matrix" = some (.ref address)) (localRow : env "r" = some (number row))
    (localWidth : env "cols" = some (number ((rows.map Prod.snd).headD []).length))
    (localBound : env "big" = some (number (bigVal (rows.map Prod.snd)))) :
    Evaluates program env initialRowExpression heap (.ref heap.length)
      (working heap (initialRow (rows.map Prod.snd) row)) := by
  apply ProjectEulerSolutions.IntegerRangeCollection.collect (values := initialRow (rows.map Prod.snd) row)
    (evaluated := .cons (Evaluates.lookup localWidth) .nil) (bounds := by simp [initialRow]; rfl)
  intro collected index inside
  have indexed : (initialRow (rows.map Prod.snd) row)[index] =
      if row = 0 ∧ index = 0 then getD2 (rows.map Prod.snd) 0 0 else bigVal (rows.map Prod.snd) := by
    simp [initialRow]
  rw [indexed]
  exact initial_cell (working heap collected) _ address row index rows
    (prefix_found heap collected address _ found)
    (fun pair member => prefix_found heap collected pair.1 _ (reads pair member))
    (by simpa [setLocal, comprehensionEnv] using localMatrix)
    (by simpa [setLocal, comprehensionEnv] using localRow) rfl
    (by simpa [setLocal, comprehensionEnv] using localBound)

end data.«project-euler-statements».data.py.project_euler_statements.p83
