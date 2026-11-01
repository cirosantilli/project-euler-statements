import data.«project-euler-statements».data.py.project_euler_statements.«p81.py.lean.d».Prefix

namespace data.«project-euler-statements».data.py.project_euler_statements.p81
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P81
open ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

abbrev rowsBody : List Stmt :=
  [.assign [.name "final"] (.call (.name "row_step") [.name "final", .name "row"])]
abbrev pathReturn : Stmt := .return (lastOrZero "final")

theorem rowsLoop_result (heap : Mutable.Heap) (env : HeapCalls.Env) (address position bufferAddress width : Nat)
    (rows : MatrixRows) (buffer : List Int)
    (contents : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2)))
    (shape : ∀ pair ∈ rows, pair.2.length = width) (size : buffer.length = width)
    (getBuffer : heap[bufferAddress]? = some (.list (encode buffer)))
    (localFinal : env "final" = some (.ref bufferAddress)) :
    ∃ extra, BlockReturns program env
      [.sequenceStepLoop "row" (.ref address) position rowsBody [], pathReturn] heap
      (number ((((rows.drop position).map Prod.snd).foldl rowStep buffer).getLast?.getD 0)) (heap ++ extra) := by
  have source : Mutable.sequence (sequenceValue (.ref address)) heap =
      some (.ok (rows.map (fun pair => .ref pair.1)), heap) := by
    simp [sequenceValue, Mutable.sequence, contents]
  by_cases active : position < rows.length
  · let pair := rows[position]
    let entered := setLocal env "row" (.ref pair.1)
    have member : pair ∈ rows := List.getElem_mem active
    have pairSize := shape pair member
    obtain ⟨extra, nextAddress, returned, nextFound⟩ := row_step.result heap bufferAddress pair.1 buffer pair.2
      getBuffer (reads pair member) (by omega)
    have called : Evaluates program entered (.call (.name "row_step") [.name "final", .name "row"])
        heap (.ref nextAddress) (heap ++ extra) := by
      apply Evaluates.call (.cons (Evaluates.lookup (by simpa [entered, setLocal] using localFinal))
        (.cons (Evaluates.lookup rfl) .nil)) returned
    let ready := setLocal entered "final" (.ref nextAddress)
    have sourceKept : (heap ++ extra)[address]? = some (.list (rows.map (fun pair => .ref pair.1))) := by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp contents).1]
      exact contents
    have readsKept : ∀ pair ∈ rows, (heap ++ extra)[pair.1]? = some (.list (encode pair.2)) := by
      intro pair member
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp (reads pair member)).1]
      exact reads pair member
    obtain ⟨more, continued⟩ := rowsLoop_result (heap ++ extra) ready address (position + 1) nextAddress width rows
      (rowStep buffer pair.2) sourceKept readsKept shape (by simp [size, pairSize]) nextFound rfl
    refine ⟨extra ++ more, ?_⟩
    have next : ((rows.drop position).map Prod.snd).foldl rowStep buffer =
        ((rows.drop (position + 1)).map Prod.snd).foldl rowStep (rowStep buffer pair.2) := by
      rw [List.drop_eq_getElem_cons active]
      rfl
    rw [next]
    apply BlockReturns.sequence_step (value := .ref pair.1) source
      (by simp [List.getElem?_eq_getElem active, pair])
    apply BlockReturns.assign called
    simpa [rowsBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, List.append_assoc] using continued
  · have gone : rows.drop position = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨[], ?_⟩
    simp only [gone, List.map_nil, List.foldl_nil, List.append_nil]
    apply BlockReturns.sequence_done source
      (by simp [List.getElem?_eq_none (by omega : rows.length ≤ position)])
    exact BlockReturns.return_value (lastOrZero_result heap env "final" bufferAddress buffer getBuffer localFinal)
termination_by rows.length - position
decreasing_by omega

end data.«project-euler-statements».data.py.project_euler_statements.p81
