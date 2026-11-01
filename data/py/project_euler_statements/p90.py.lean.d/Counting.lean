import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».CountRows

/-! The reference's enumerate/slice traversal counts unordered positional pairs. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p90.counting
open FormalSW.PyAst HeapCalls ProjectEulerSolutions DigitDice
open choose_faces (Row)
set_option Elab.async false

/-- A suffix slice copies only the references; display checks retain the original dice. -/
theorem row (required : Required) (left : Row) (rows : List Row) (address position count : Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (following : List Stmt) (post : Mutable.Value → Mutable.Heap → Prop)
    (valid : required.Valid heap) (leftValid : left.Valid heap)
    (rowsValid : ∀ row ∈ rows, row.Valid heap)
    (found : heap[address]? = some (.list (rows.map Row.reference)))
    (getCubes : env "cubes" = some (.ref address)) (getIndex : env "i" = some (number position))
    (getLeft : env "a" = some left.reference) (getRequired : env "required_pairs" = some (.ref required.address))
    (getCount : env "pairs" = some (number count))
    (continued : ∀ extra afterEnv, afterEnv "pairs" = some (number (count + (rows.drop position).countP (test required left))) →
      Keep env afterEnv → HeapMemoCalls.BlockReturnsRel program spec afterEnv following (heap ++ extra) post globals) :
    HeapMemoCalls.BlockReturnsRel program spec env (outerBody ++ following) heap post globals := by
  let added : Mutable.Heap := [.list ((rows.drop position).map Row.reference)]
  have sliced : Evaluates program env (.subscript (.name "cubes") (.slice (some (.name "i")) none none))
      heap (.ref heap.length) (heap ++ added) globals := by
    apply Evaluates.slice (.cons (Evaluates.lookup getCubes) (.cons (Evaluates.lookup getIndex)
      (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
    simpa [added] using Mutable.getSlice_list_suffix heap address (rows.map Row.reference) position found
  apply HeapMemoCalls.BlockReturnsRel.for_sequence_heap cache_disjoint (by intros; simp) sliced
    (expand69.pool.preserves_append heap added) (items := (rows.drop position).map Row.reference)
  · simp [Mutable.sequence, added]
  · apply row_loop required left (rows.drop position) (rows.drop position) heap.length 0 count
      (heap ++ added) env globals following post (valid.append added) (row_valid_append left heap added leftValid)
      (fun item member => row_valid_append item heap added (rowsValid item (List.mem_of_mem_drop member)))
      (by simp [added]) rfl getLeft getRequired getCount
    intro extra afterEnv total kept
    simpa only [List.append_assoc] using continued (added ++ extra) afterEnv total kept

/-- The index and current die advance together; each suffix includes the identical-design pair once. -/
theorem outer_loop (required : Required) (rows remaining : List Row) (address position count : Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (valid : required.Valid heap) (rowsValid : ∀ row ∈ rows, row.Valid heap)
    (found : heap[address]? = some (.list (rows.map Row.reference))) (suffix : rows.drop position = remaining)
    (getCubes : env "cubes" = some (.ref address)) (getRequired : env "required_pairs" = some (.ref required.address))
    (getCount : env "pairs" = some (number count)) :
    HeapMemoCalls.BlockReturnsRel program spec env
      [.enumerateStepLoop "i" "a" (.ref address) position position outerBody [], .return (.name "pairs")] heap
      (fun value after => value = number (count + countPairs (test required) remaining) ∧ ∃ extra, after = heap ++ extra) globals := by
  induction remaining generalizing position count heap env with
  | nil =>
      apply HeapMemoCalls.BlockReturnsRel.enumerate_done (items := rows.map Row.reference)
        (by simp [sequenceValue, Mutable.sequence, found])
      · have missing : rows[position]? = none := List.getElem?_eq_none_iff.mpr (List.drop_eq_nil_iff.mp suffix)
        simp [missing]
      · apply HeapMemoCalls.BlockReturnsRel.return_value
        apply (HeapMemoCalls.Evaluates.lookup getCount).rel.consequence
        rintro value after ⟨rfl, rfl⟩
        exact ⟨rfl, [], by simp⟩
  | cons first rest ih =>
      have item : rows[position]? = some first := by
        simpa [suffix] using (List.head?_drop (l := rows) (i := position)).symm
      have member : first ∈ rows := List.mem_of_getElem? item
      let bound := setLocal (setLocal env "i" (number position)) "a" first.reference
      have cubesBound : bound "cubes" = some (.ref address) := by simpa [bound, setLocal] using getCubes
      have requiredBound : bound "required_pairs" = some (.ref required.address) := by simpa [bound, setLocal] using getRequired
      have countBound : bound "pairs" = some (number count) := by simpa [bound, setLocal] using getCount
      apply HeapMemoCalls.BlockReturnsRel.enumerate_step (items := rows.map Row.reference) (value := first.reference)
        (by simp [sequenceValue, Mutable.sequence, found]) (by simp [item])
      apply row required first rows address position count heap bound globals _ _ valid (rowsValid first member)
        rowsValid found cubesBound (by simp [bound, setLocal]) rfl requiredBound countBound
      intro extra afterEnv total kept
      have afterCubes : afterEnv "cubes" = some (.ref address) := by
        rw [kept "cubes" (by decide) (by decide)]; exact cubesBound
      have afterRequired : afterEnv "required_pairs" = some (.ref required.address) := by
        rw [kept "required_pairs" (by decide) (by decide)]; exact requiredBound
      have tail : rows.drop (position + 1) = rest := by simp [List.drop_add_one_eq_tail_drop, suffix]
      have finished := ih (position + 1) (count + (rows.drop position).countP (test required first))
        (heap ++ extra) afterEnv (valid.append extra)
        (fun row mem => row_valid_append row heap extra (rowsValid row mem))
        (HeapCollection.prefix_found heap extra address _ found) tail afterCubes afterRequired total
      apply HeapMemoCalls.BlockReturnsRel.consequence
        (by simpa only [Int.natCast_add, Int.natCast_one] using finished)
      rintro value after ⟨same, more, shape⟩
      refine ⟨?_, extra ++ more, by simpa only [List.append_assoc] using shape⟩
      simpa only [countPairs, suffix, Nat.add_assoc] using same

/-- The complete parsed outer loop returns the unordered-pair count for any valid list of dice. -/
theorem result (required : Required) (rows : List Row) (address count : Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (valid : required.Valid heap) (rowsValid : ∀ row ∈ rows, row.Valid heap)
    (found : heap[address]? = some (.list (rows.map Row.reference)))
    (getCubes : env "cubes" = some (.ref address)) (getRequired : env "required_pairs" = some (.ref required.address))
    (getCount : env "pairs" = some (number count)) :
    HeapMemoCalls.BlockReturnsRel program spec env (code.drop 2) heap
      (fun value after => value = number (count + countPairs (test required) rows) ∧ ∃ extra, after = heap ++ extra) globals := by
  apply HeapMemoCalls.BlockReturnsRel.for_enumerate (HeapMemoCalls.Evaluates.lookup getCubes)
    (items := rows.map Row.reference)
  · simp [Mutable.sequence, found]
  · exact outer_loop required rows rows address 0 count heap env globals valid rowsValid found rfl getCubes getRequired getCount

end data.«project-euler-statements».data.py.project_euler_statements.p90.counting
