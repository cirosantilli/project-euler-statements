import data.«project-euler-statements».data.py.project_euler_statements.«p82.py.lean.d».Add
import data.«project-euler-statements».data.py.project_euler_statements.«p82.py.lean.d».Reverse
import ProjectEulerSolutions.Lib.IntegerListMinimumCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p82
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P82
open ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

abbrev minimumOrZero : Expr := .ifExp (.name "final") (.builtinCall .min [.name "final"]) (.constant (.int 0))
abbrev outerBody : List Stmt :=
  [.assign [.name "base"] (.call (.name "add_lists") [.name "final", .name "col"]),
   .assign [.name "final"] (.call (.name "relax_up") [.call (.name "relax_down") [.name "base", .name "col"], .name "col"])]

theorem minimumOrZero_result (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat) (values : List Int)
    (found : heap[address]? = some (.list (encode values))) (localValue : env "final" = some (.ref address)) :
    Evaluates program env minimumOrZero heap (number (minimum values)) heap := by
  cases values with
  | nil =>
      exact Evaluates.conditional (flag := false) (Evaluates.lookup localValue)
        (by simp [Mutable.truth, found, encode]) Evaluates.constant
  | cons first rest =>
      apply Evaluates.conditional (flag := true) (Evaluates.lookup localValue) (by simp [Mutable.truth, found, encode])
      exact ProjectEulerSolutions.IntegerListMinimumCalls.minimum_evaluate program "final" first rest heap env address localValue found

theorem rows_loop (heap : Mutable.Heap) (env : HeapCalls.Env) (address position bufferAddress height : Nat)
    (rows : MatrixRows) (buffer : List Int)
    (contents : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2)))
    (shape : ∀ pair ∈ rows, pair.2.length = height) (size : buffer.length = height)
    (getBuffer : heap[bufferAddress]? = some (.list (encode buffer)))
    (localFinal : env "final" = some (.ref bufferAddress)) :
    ∃ extra, BlockReturns program env
      [.sequenceStepLoop "col" (.ref address) position outerBody [], .return minimumOrZero] heap
      (number (minimum (((rows.drop position).map Prod.snd).foldl columnStep buffer))) (heap ++ extra) := by
  have source : Mutable.sequence (sequenceValue (.ref address)) heap =
      some (.ok (rows.map (fun pair => .ref pair.1)), heap) := by simp [sequenceValue, Mutable.sequence, contents]
  by_cases active : position < rows.length
  · let pair := rows[position]
    let entered := setLocal env "col" (.ref pair.1)
    have member : pair ∈ rows := List.getElem_mem active
    have pairSize := shape pair member
    have same : buffer.length = pair.2.length := by omega
    obtain ⟨added, addReturn, addFound⟩ := add_lists.result heap bufferAddress pair.1 buffer pair.2 getBuffer (reads pair member) same
    have addCall : Evaluates program entered (.call (.name "add_lists") [.name "final", .name "col"])
        heap (.ref heap.length) (heap ++ added) :=
      Evaluates.call (.cons (Evaluates.lookup (by simpa [entered, setLocal] using localFinal)) (.cons (Evaluates.lookup rfl) .nil)) addReturn
    have colAdded : (heap ++ added)[pair.1]? = some (.list (encode pair.2)) := by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp (reads pair member)).1]
      exact reads pair member
    let withBase := setLocal entered "base" (.ref heap.length)
    obtain ⟨downExtra, downAddress, downReturn, downFound⟩ := relax_down.result (heap ++ added) heap.length pair.1
      (addLists buffer pair.2) pair.2 addFound colAdded (by simp [same])
    have downCall : Evaluates program withBase (.call (.name "relax_down") [.name "base", .name "col"])
        (heap ++ added) (.ref downAddress) ((heap ++ added) ++ downExtra) :=
      Evaluates.call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) downReturn
    have colDown : ((heap ++ added) ++ downExtra)[pair.1]? = some (.list (encode pair.2)) := by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp colAdded).1]
      exact colAdded
    have addedSize := addLists_length buffer pair.2 same
    have downSize := relaxDown_length (addLists buffer pair.2) pair.2 (by omega)
    obtain ⟨upExtra, upAddress, upReturn, upFound⟩ := relax_up.result ((heap ++ added) ++ downExtra) downAddress pair.1
      (relaxDown (addLists buffer pair.2) pair.2) pair.2 downFound colDown (by omega)
    have upCall : Evaluates program withBase
        (.call (.name "relax_up") [.call (.name "relax_down") [.name "base", .name "col"], .name "col"])
        (heap ++ added) (.ref upAddress) (((heap ++ added) ++ downExtra) ++ upExtra) :=
      Evaluates.call (.cons downCall (.cons (Evaluates.lookup rfl) .nil)) upReturn
    let nextHeap := ((heap ++ added) ++ downExtra) ++ upExtra
    let ready := setLocal withBase "final" (.ref upAddress)
    have kept (address : Nat) (object : Mutable.Object) (found : heap[address]? = some object) :
        nextHeap[address]? = some object := by
      simp only [nextHeap, List.append_assoc]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
      exact found
    obtain ⟨more, continued⟩ := rows_loop nextHeap ready address (position + 1) upAddress height rows (columnStep buffer pair.2)
      (kept _ _ contents) (fun pair member => kept _ _ (reads pair member)) shape
      ((columnStep_length buffer pair.2 same).trans size) upFound rfl
    have next : ((rows.drop position).map Prod.snd).foldl columnStep buffer =
        ((rows.drop (position + 1)).map Prod.snd).foldl columnStep (columnStep buffer pair.2) := by
      rw [List.drop_eq_getElem_cons active]
      rfl
    refine ⟨added ++ downExtra ++ upExtra ++ more, ?_⟩
    rw [next]
    apply BlockReturns.sequence_step (value := .ref pair.1) source (by simp [List.getElem?_eq_getElem active, pair])
    apply BlockReturns.assign addCall
    apply BlockReturns.assign upCall
    simpa [outerBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, nextHeap, List.append_assoc] using continued
  · have gone : rows.drop position = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨[], ?_⟩
    simp only [gone, List.map_nil, List.foldl_nil, List.append_nil]
    exact BlockReturns.sequence_done source (by simp [List.getElem?_eq_none (by omega : rows.length ≤ position)])
      (BlockReturns.return_value (minimumOrZero_result heap env bufferAddress buffer getBuffer localFinal))
termination_by rows.length - position
decreasing_by omega

end data.«project-euler-statements».data.py.project_euler_statements.p82
