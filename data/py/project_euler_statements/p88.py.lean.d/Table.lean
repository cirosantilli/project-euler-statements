import data.«project-euler-statements».data.py.project_euler_statements.«p88.py.lean.d».Arithmetic
import ProjectEulerSolutions.Lib.ProductSumSearchSteps
import ProjectEulerSolutions.Lib.HeapTables

namespace data.«project-euler-statements».data.py.project_euler_statements.p88
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.ProductSumNumbers
set_option Elab.async false

abbrev encode (items : List Nat) : List Mutable.Value := items.map number
def working (base : Mutable.Heap) (best : List Nat) : Mutable.Heap := base ++ [.list (encode best)]
abbrev sizeTest : Expr := .compare (.name "k") [(.ltE, .name "k_max")]
abbrev improveTest : Expr := .boolOp .and
  [sizeTest, .compare (.name "new_prod") [(.lt, .subscript (.name "best") (.name "k"))]]

theorem working_found (base : Mutable.Heap) (best : List Nat) :
    (working base best)[base.length]? = some (.list (encode best)) := by simp [working]

theorem size_evaluate (size maxSize : Nat) (env : HeapCalls.Env) (heap : Mutable.Heap)
    (getSize : env "k" = some (number size)) (getMax : env "k_max" = some (number maxSize)) :
    Evaluates program env sizeTest heap (.scalar (.bool (decide (size ≤ maxSize)))) heap := by
  apply Evaluates.compare (Evaluates.lookup getSize) (Evaluates.lookup getMax)
  simp [HeapCalls.compare, scalarCompare, evalCmpOp]

theorem best_value (best : List Nat) (size : Nat) (inside : size < best.length)
    (base : Mutable.Heap) (env : HeapCalls.Env)
    (getTable : env "best" = some (.ref base.length)) (getSize : env "k" = some (number size)) :
    Evaluates program env (.subscript (.name "best") (.name "k")) (working base best)
      (number (best[size]?.getD 0)) (working base best) := by
  apply Evaluates.subscript (by intros; simp) (Evaluates.lookup getTable) (Evaluates.lookup getSize)
  simpa [encode, inside] using Mutable.getItem_list (working base best) base.length size
    (encode best) (working_found base best) (by simpa using inside)

theorem improve (maxSize : Nat) (best : List Nat) (size value : Nat)
    (accepted : size ≤ maxSize) (inside : size < best.length)
    (base : Mutable.Heap) (env : HeapCalls.Env)
    (getTable : env "best" = some (.ref base.length))
    (getMax : env "k_max" = some (number maxSize))
    (getSize : env "k" = some (number size)) (getValue : env "new_prod" = some (number value)) :
    BlockContinues program env [dfsBody[4]'(by decide)] (working base best) env
      (working base (relax best (size, value))) := by
  have compared : Evaluates program env
      (.compare (.name "new_prod") [(.lt, .subscript (.name "best") (.name "k"))])
      (working base best) (.scalar (.bool (decide (value < best[size]?.getD 0)))) (working base best) := by
    apply Evaluates.compare (Evaluates.lookup getValue) (best_value best size inside base env getTable getSize)
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  have tested : Evaluates program env improveTest (working base best)
      (.scalar (.bool (decide (value < best[size]?.getD 0)))) (working base best) := by
    apply Evaluates.boolean_next (flag := true) (size_evaluate size maxSize env (working base best) getSize getMax)
      (by simp [Mutable.truth, scalarTruth, accepted]) rfl
    exact Evaluates.boolean_last (flag := decide (value < best[size]?.getD 0)) compared
      (by simp [Mutable.truth, scalarTruth])
  rw [relax_guarded best size value inside]
  by_cases smaller : value < best[size]?.getD 0
  · rw [if_pos smaller]
    apply BlockContinues.branch (flag := true) tested (by simp [Mutable.truth, scalarTruth, smaller])
    apply BlockContinues.setItem (value := number value) (receiver := .ref base.length)
      (subscript := number size) (by intros; simp) (Evaluates.lookup getValue)
      (.cons (Evaluates.lookup getTable) (.cons (Evaluates.lookup getSize) .nil))
    simpa [working, encode, List.map_set, List.set_append_right] using
      ProjectEulerSolutions.HeapTables.setItem_list (working base best) base.length size
        (encode best) (number value) (working_found base best) (by simpa using inside)
  · rw [if_neg smaller]
    exact BlockContinues.branch (flag := false) tested (by simp [Mutable.truth, scalarTruth, smaller]) .nil

/-- A rejected size skips both the table access and the recursive call. -/
theorem reject (maxSize size : Nat) (tooLarge : maxSize < size)
    (env : HeapCalls.Env) (heap : Mutable.Heap)
    (getSize : env "k" = some (number size)) (getMax : env "k_max" = some (number maxSize)) :
    BlockContinues program env ((dfsBody.drop 4).take 2) heap env heap := by
  have tested := size_evaluate size maxSize env heap getSize getMax
  have short : Evaluates program env improveTest heap (.scalar (.bool (decide (size ≤ maxSize)))) heap :=
    Evaluates.boolean_stop (flag := false) tested (by simp [Mutable.truth, scalarTruth]; omega) rfl
  have first : BlockContinues program env [dfsBody[4]'(by decide)] heap env heap :=
    BlockContinues.branch (flag := false) short (by simp [Mutable.truth, scalarTruth]; omega) .nil
  have second : BlockContinues program env [dfsBody[5]'(by decide)] heap env heap :=
    BlockContinues.branch (flag := false) tested (by simp [Mutable.truth, scalarTruth]; omega) .nil
  exact first.append second

end data.«project-euler-statements».data.py.project_euler_statements.p88
