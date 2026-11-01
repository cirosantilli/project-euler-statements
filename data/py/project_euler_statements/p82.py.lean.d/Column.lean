import data.«project-euler-statements».data.py.project_euler_statements.«p82.py.lean.d».Inputs
import ProjectEulerSolutions.Lib.TriangleBufferCalls
import ProjectEulerStatements.Lib.GridPathColumns

namespace data.«project-euler-statements».data.py.project_euler_statements.p82
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P82
open ProjectEulerSolutions.RectangularMatrixCalls (MatrixRows)
open ProjectEulerSolutions.TriangleBufferCalls
set_option Elab.async false

abbrev columnElement : Expr := .ifExp
  (.compare (.name "c") [(.lt, .builtinCall .len [.name "row"])])
  (.subscript (.name "row") (.name "c")) (.constant (.int 0))
abbrev columnComprehension : Expr := .listComp columnElement [("row", .name "matrix", [])]

theorem column_element (heap : Mutable.Heap) (env : HeapCalls.Env) (address col : Nat) (row : List Int)
    (contents : heap[address]? = some (.list (encode row)))
    (localRow : env "row" = some (.ref address)) (localColumn : env "c" = some (number col)) :
    Evaluates program env columnElement heap (number (row.getD col 0)) heap := by
  have length : Evaluates program env (.builtinCall .len [.name "row"]) heap (number row.length) heap :=
    Evaluates.builtin (.cons (Evaluates.lookup localRow) .nil) (by simp [HeapCalls.primitive, Mutable.length, contents, encode])
  have tested : Evaluates program env (.compare (.name "c") [(.lt, .builtinCall .len [.name "row"])])
      heap (.scalar (.bool (decide (col < row.length)))) heap := by
    apply Evaluates.compare (Evaluates.lookup localColumn) length
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  by_cases inside : col < row.length
  · apply Evaluates.conditional (flag := true) (by simpa only [inside, decide_true] using tested) rfl
    exact index_evaluates program heap env "row" address col row _ (.name "c") localRow
      (Evaluates.lookup localColumn) (by intros a b c impossible; cases impossible) contents
      (by simp [List.getD, List.getElem?_eq_getElem inside])
  · apply Evaluates.conditional (flag := false) (by simpa only [inside, decide_false] using tested) rfl
    simpa [List.getD, List.getElem?_eq_none (by omega : row.length ≤ col)] using
      (Evaluates.constant (module := program) (env := env) (heap := heap) (value := Constant.int 0))

theorem column_loop (base : Mutable.Heap) (env : HeapCalls.Env) (address position col : Nat)
    (rows : MatrixRows) (output : List Int)
    (getMatrix : base[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (getRows : ∀ pair ∈ rows, base[pair.1]? = some (.list (encode pair.2)))
    (localColumn : env "c" = some (number col)) :
    ∃ after, BlockContinues program env
      [.sequenceStepLoop "row" (.ref address) position [.comprehensionAppend base.length columnElement] []]
      (working base output) after
      (working base (output ++ (getCol (rows.map Prod.snd) col).drop position)) := by
  have source : Mutable.sequence (.ref address) (working base output) =
      some (.ok (rows.map (fun pair => .ref pair.1)), working base output) := by
    simp [Mutable.sequence, prefix_found base output address _ getMatrix]
  by_cases active : position < rows.length
  · let pair := rows[position]
    let value := pair.2.getD col 0
    let entered := setLocal env "row" (.ref pair.1)
    have item : (rows.map (fun pair => Mutable.Value.ref pair.1))[position]? = some (.ref pair.1) := by
      simp [List.getElem?_eq_getElem active, pair]
    have evaluated := column_element (working base output) entered pair.1 col pair.2
      (prefix_found base output pair.1 _ (getRows pair (List.getElem_mem active))) rfl
      (by simpa [entered, setLocal] using localColumn)
    have appended := BlockContinues.comprehension_append evaluated (found base output)
    have write : (working base output).set base.length (.list (encode output ++ [number value])) =
        working base (output ++ [value]) := by simp [working, encode]
    rw [write] at appended
    obtain ⟨after, continued⟩ := column_loop base entered address (position + 1) col rows (output ++ [value]) getMatrix getRows
      (by simpa [entered, setLocal] using localColumn)
    have inColumn : position < (getCol (rows.map Prod.snd) col).length := by simpa [getCol] using active
    have selected : (getCol (rows.map Prod.snd) col)[position] = value := by simp [getCol, pair, value]
    refine ⟨after, ?_⟩
    apply BlockContinues.sequence_step (source := .ref address) source item
    simpa only [List.drop_eq_getElem_cons inColumn, selected, Calls.loopContinuation, Calls.loopControl,
      Calls.loopControlStmt, Bool.false_or, Bool.false_eq_true, if_false, List.append_assoc, List.singleton_append] using appended.append continued
  · have gone : (getCol (rows.map Prod.snd) col).drop position = [] := by
      apply List.drop_eq_nil_iff.mpr
      simpa [getCol] using (show rows.length ≤ position by omega)
    refine ⟨env, ?_⟩
    rw [gone, List.append_nil]
    exact BlockContinues.sequence_done (source := .ref address) source
      (by simp [List.getElem?_eq_none (by omega : rows.length ≤ position)]) BlockContinues.nil
termination_by rows.length - position
decreasing_by omega

theorem get_col.result (heap : Mutable.Heap) (address col : Nat) (rows : MatrixRows)
    (getMatrix : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (getRows : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2))) :
    ReturnsValue program "get_col" [.ref address, number col] heap (.ref heap.length)
      (working heap (getCol (rows.map Prod.snd) col)) := by
  let args : List Arg :=
    [⟨"matrix", some (.subscript (.name "list") (.subscript (.name "list") (.name "int"))), none⟩,
     ⟨"c", some (.name "int"), none⟩]
  let entry := argumentEnv args [.ref address, number col]
  let masked := comprehensionEnv entry [("row", .name "matrix", [])]
  obtain ⟨after, loop⟩ := column_loop heap masked address 0 col rows [] getMatrix getRows rfl
  apply BlockReturns.function (args := args) rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.list_comp_sequence (items := rows.map (fun pair => .ref pair.1))
    (by intros expressions impossible; cases impossible) (Evaluates.lookup rfl)
    (by simp [Mutable.sequence, getMatrix])
  simpa [masked, working, encode, comprehensionFilters, comprehensionBody] using loop

end data.«project-euler-statements».data.py.project_euler_statements.p82
