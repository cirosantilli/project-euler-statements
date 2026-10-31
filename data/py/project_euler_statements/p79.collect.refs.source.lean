import data.«project-euler-statements».data.py.project_euler_statements.«p79.edges.source»

/-! Appending a separate source list to a comprehension collector retains all element references. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

theorem set_same_object (heap : Mutable.Heap) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) : heap.set address object = heap := by
  obtain ⟨bounded, contents⟩ := List.getElem?_eq_some_iff.mp found
  rw [← contents]
  exact List.set_getElem_self bounded

theorem collect_refs_loop (heap : Mutable.Heap) (address collector : Nat)
    (items before remaining collected : List Mutable.Value)
    (found : heap[address]? = some (.list items))
    (outputFound : heap[collector]? = some (.list collected)) (distinct : address ≠ collector)
    (partition : items = before ++ remaining) (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "e" (.ref address) before.length
        [.comprehensionAppend collector (.name "e")] []]
      heap finalEnv (heap.set collector (.list (collected ++ remaining))) := by
  induction remaining generalizing heap before collected env with
  | nil =>
      refine ⟨env, ?_⟩
      simp only [List.append_nil, set_same_object heap collector _ outputFound]
      apply BlockContinues.sequence_done (items := items)
        (by simp [sequenceValue, Mutable.sequence, found])
      · simp [partition]
      · exact .nil
  | cons item rest ih =>
      let bound := setLocal env "e" item
      let updated := heap.set collector (.list (collected ++ [item]))
      have appended : BlockContinues program bound
          [.comprehensionAppend collector (.name "e")] heap bound updated :=
        BlockContinues.comprehension_append
          (Evaluates.lookup (by simp [bound, setLocal])) outputFound
      have input : updated[address]? = some (.list items) := by
        simpa [updated, Ne.symm distinct] using found
      have output : updated[collector]? = some (.list (collected ++ [item])) := by
        simp [updated, (List.getElem?_eq_some_iff.mp outputFound).1]
      obtain ⟨finalEnv, continued⟩ := ih updated (before ++ [item]) (collected ++ [item])
        input output (by simpa [List.append_assoc] using partition) bound
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.sequence_step (items := items) (value := item)
        (by simp [sequenceValue, Mutable.sequence, found]) (by simp [partition])
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        List.append_assoc, updated, bound] using appended.append continued

theorem stored_after_list_write (heap : Mutable.Heap) (address : Nat)
    (old values : List Mutable.Value) (found : heap[address]? = some (.list old))
    (entry : Edge) (stored : Stored heap entry) :
    Stored (heap.set address (.list values)) entry := by
  have different : address ≠ entry.1 := by
    intro same
    change heap[entry.1]? = _ at stored
    rw [← same, found] at stored
    cases stored
  simpa [Stored, different] using stored

end data.«project-euler-statements».data.py.project_euler_statements.p79
