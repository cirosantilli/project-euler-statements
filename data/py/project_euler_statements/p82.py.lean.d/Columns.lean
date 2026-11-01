import data.«project-euler-statements».data.py.project_euler_statements.«p82.py.lean.d».Column

namespace data.«project-euler-statements».data.py.project_euler_statements.p82
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P82
open ProjectEulerSolutions.RectangularMatrixCalls (MatrixRows)
open ProjectEulerSolutions.TriangleBufferCalls
set_option Elab.async false

def columnRefs (base : Mutable.Heap) (count : Nat) : List Mutable.Value :=
  (List.range count).map (fun index => .ref (base.length + 1 + index))
def columnsHeap (base : Mutable.Heap) (rows : MatrixRows) (count : Nat) : Mutable.Heap :=
  base ++ [.list (columnRefs base count)] ++
    (List.range count).map (fun index => .list (encode (getCol (rows.map Prod.snd) index)))

@[simp] theorem columnsHeap_length (base : Mutable.Heap) (rows : MatrixRows) (count : Nat) :
    (columnsHeap base rows count).length = base.length + 1 + count := by simp [columnsHeap]; omega

theorem columnsHeap_read (base : Mutable.Heap) (rows : MatrixRows) (count address : Nat) (object : Mutable.Object)
    (found : base[address]? = some object) : (columnsHeap base rows count)[address]? = some object := by
  unfold columnsHeap
  rw [List.append_assoc, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem columnsHeap_advance (base : Mutable.Heap) (rows : MatrixRows) (count : Nat) :
    ((columnsHeap base rows count) ++ [Mutable.Object.list (encode (getCol (rows.map Prod.snd) count))]).set base.length
      (Mutable.Object.list (columnRefs base count ++ [Mutable.Value.ref (columnsHeap base rows count).length])) = columnsHeap base rows (count + 1) := by
  simp [columnsHeap, columnRefs, List.range_succ, List.append_assoc]; omega

abbrev columnsElement : Expr := .call (.name "get_col") [.name "matrix", .name "c"]
abbrev columnsRange : List Expr := [.builtinCall .len [.subscript (.name "matrix") (.constant (.int 0))]]
abbrev columnsComprehension : Expr := .listComp columnsElement [("c", .call (.name "range") columnsRange, [])]

theorem columns_loop (base : Mutable.Heap) (env : HeapCalls.Env) (address cursor width : Nat) (rows : MatrixRows)
    (getMatrix : base[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (getRows : ∀ pair ∈ rows, base[pair.1]? = some (.list (encode pair.2)))
    (bounded : cursor ≤ width) (localMatrix : env "matrix" = some (.ref address)) :
    ∃ after, BlockContinues program env
      [.rangeStepLoop "c" cursor width 1 [.comprehensionAppend base.length columnsElement] []]
      (columnsHeap base rows cursor) after (columnsHeap base rows width) := by
  by_cases active : cursor < width
  · let entered := setLocal env "c" (number cursor)
    let state := columnsHeap base rows cursor
    have called : Evaluates program entered columnsElement state (.ref state.length)
        (state ++ [.list (encode (getCol (rows.map Prod.snd) cursor))]) := by
      apply Evaluates.call (.cons (Evaluates.lookup (by simpa [entered, setLocal] using localMatrix))
        (.cons (Evaluates.lookup rfl) .nil))
      exact get_col.result state address cursor rows (columnsHeap_read base rows cursor address _ getMatrix)
        (fun pair member => columnsHeap_read base rows cursor pair.1 _ (getRows pair member))
    have found : (state ++ [.list (encode (getCol (rows.map Prod.snd) cursor))])[base.length]? =
        some (.list (columnRefs base cursor)) := by simp [state, columnsHeap, List.append_assoc]
    have emitted := BlockContinues.comprehension_append called found
    rw [columnsHeap_advance] at emitted
    obtain ⟨after, continued⟩ := columns_loop base entered address (cursor + 1) width rows getMatrix getRows (by omega)
      (by simpa [entered, setLocal] using localMatrix)
    refine ⟨after, ?_⟩
    apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
    simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_or, Bool.false_eq_true,
      if_false, Int.natCast_add, Int.natCast_one] using emitted.append continued
  · have done : cursor = width := by omega
    subst cursor
    exact ⟨env, BlockContinues.range_done (by simp [Calls.rangeContinues]) BlockContinues.nil⟩
termination_by width - cursor
decreasing_by omega

theorem columns_allocation (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat)
    (first : Nat × List Int) (rest : MatrixRows)
    (getMatrix : heap[address]? = some (.list ((first :: rest).map (fun pair => .ref pair.1))))
    (getRows : ∀ pair ∈ first :: rest, heap[pair.1]? = some (.list (encode pair.2)))
    (localMatrix : env "matrix" = some (.ref address)) :
    Evaluates program env columnsComprehension heap (.ref heap.length) (columnsHeap heap (first :: rest) first.2.length) := by
  have firstRead : Evaluates program env (.subscript (.name "matrix") (.constant (.int 0))) heap (.ref first.1) heap := by
    apply Evaluates.subscript (by intros a b c impossible; cases impossible) (Evaluates.lookup localMatrix) Evaluates.constant
    simp [Mutable.getItem, Mutable.index, getMatrix, Except.map]
  have width : Evaluates program env (.builtinCall .len [.subscript (.name "matrix") (.constant (.int 0))])
      heap (number first.2.length) heap := by
    exact Evaluates.builtin (.cons firstRead .nil)
      (by simp [HeapCalls.primitive, Mutable.length, getRows first (by simp), encode])
  let masked := comprehensionEnv env [("c", .call (.name "range") columnsRange, [])]
  obtain ⟨after, loop⟩ := columns_loop heap masked address 0 first.2.length (first :: rest) getMatrix getRows (by omega)
    (by simpa [masked, comprehensionEnv] using localMatrix)
  apply Evaluates.list_comp_range (.cons width .nil) rfl
  simpa [columnsHeap, columnRefs, comprehensionBody, comprehensionFilters] using loop

end data.«project-euler-statements».data.py.project_euler_statements.p82
