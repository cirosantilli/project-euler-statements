import data.«project-euler-statements».data.py.project_euler_statements.«p79.collect.edge.source»
import data.«project-euler-statements».data.py.project_euler_statements.«p79.dedup.source»

/-! The reference edge builder collects all observations and removes duplicate pair contents. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def attemptEdges (attempts : List String) : List (String × String) :=
  attempts.flatMap observationPairs

def collectEdges : Expr := .listComp (.name "e")
  [("s", .name "attempts", []), ("e", .call (.name "edges_from") [.name "s"], [])]

theorem edges_source : executableBody
    ((findFunctionIn program.body "edges").getD ([], [])).2 =
      [.return (.call (.name "erase_dups") [collectEdges])] := rfl

theorem collect_edges_loop (heap : Mutable.Heap) (address collector : Nat)
    (attempts before remaining : List String) (collected : List Edge)
    (found : heap[address]? = some (.list (attempts.map text)))
    (edges : Edges heap collector collected) (distinct : address ≠ collector)
    (partition : attempts = before ++ remaining) (env : HeapCalls.Env) :
    ∃ after entries finalEnv,
      BlockContinues program env
        [.sequenceStepLoop "s" (.ref address) before.length (collectEdgeBody collector) []]
        heap finalEnv after ∧
      Edges after collector entries ∧ entries.map Prod.snd = collected.map Prod.snd ++
        attemptEdges remaining ∧ heap.length ≤ after.length ∧
      (∀ index < heap.length, index ≠ collector → after[index]? = heap[index]?) := by
  induction remaining generalizing heap before collected env with
  | nil =>
      refine ⟨heap, collected, env, ?_, edges, by simp [attemptEdges], le_rfl, by intros; rfl⟩
      apply BlockContinues.sequence_done (items := attempts.map text)
        (by simp [sequenceValue, Mutable.sequence, found])
      · simp [partition]
      · exact .nil
  | cons s rest ih =>
      let bound := setLocal env "s" (text s)
      obtain ⟨middle, current, middleEnv, stepped, currentEdges, currentPairs, grew, preserved⟩ :=
        collect_edge_step heap collector collected edges bound s (by simp [bound, setLocal])
      have input : middle[address]? = some (.list (attempts.map text)) :=
        (preserved address (List.getElem?_eq_some_iff.mp found).1 distinct).trans found
      obtain ⟨after, entries, finalEnv, continued, finalEdges, finalPairs, grewAgain, saved⟩ :=
        ih middle (before ++ [s]) current input currentEdges
          (by simpa [List.append_assoc] using partition) middleEnv
      refine ⟨after, entries, finalEnv, ?_, finalEdges, ?_, grew.trans grewAgain, ?_⟩
      · apply BlockContinues.sequence_step (items := attempts.map text) (value := text s)
          (by simp [sequenceValue, Mutable.sequence, found]) (by simp [partition])
        simpa [collectEdgeBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          bound] using stepped.append continued
      · rw [finalPairs, currentPairs]
        simp [attemptEdges, List.append_assoc]
      · intro index bounded different
        exact (saved index (lt_of_lt_of_le bounded grew) different).trans
          (preserved index bounded different)

theorem collect_edges_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text)))
    (env : HeapCalls.Env) (getAttempts : env "attempts" = some (.ref address)) :
    ∃ after entries,
      Evaluates program env collectEdges heap (.ref heap.length) after ∧
      Edges after heap.length entries ∧ entries.map Prod.snd = attemptEdges attempts ∧
      heap <+: after := by
  have bounded := (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨after, entries, finalEnv, collected, edges, contents, _, preserved⟩ :=
    collect_edges_loop (heap ++ [.list []]) address heap.length attempts [] attempts []
      (by simp [List.getElem?_append_left bounded, found])
      ⟨by simp, by simp⟩ (by omega) rfl
      (comprehensionEnv env
        [("s", .name "attempts", []), ("e", .call (.name "edges_from") [.name "s"], [])])
  refine ⟨after, entries, ?_, edges, by simpa using contents, ?_⟩
  · apply Evaluates.list_comp_sequence (items := attempts.map text)
      (by intros; intro impossible; cases impossible) (Evaluates.lookup getAttempts)
      (by simp [Mutable.sequence, found])
    exact collected
  · apply List.prefix_iff_getElem?.mpr
    intro index inside
    have retained := preserved index (by simp; omega) (by omega)
    simpa [List.getElem?_append_left inside, List.getElem?_eq_getElem inside] using retained

/-- Distinct logical edges retain their source tuple objects; the caller's heap is a prefix. -/
theorem edges_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text))) :
    ∃ after resultAddress entries,
      ReturnsValue program "edges" [.ref address] heap (.ref resultAddress) after ∧
      Edges after resultAddress entries ∧ (entries.map Prod.snd).Nodup ∧
      (∀ pair, pair ∈ entries.map Prod.snd ↔ pair ∈ attemptEdges attempts) ∧
      heap <+: after := by
  let source := (findFunctionIn program.body "edges").getD ([], [])
  let env := functionEnv source.1 source.2 [.ref address] []
  obtain ⟨collectedHeap, collected, collectedSource, collectedEdges, contents, retained⟩ :=
    collect_edges_result heap address attempts found env rfl
  let entries := dedupBy Prod.snd [] collected
  let after := collectedHeap ++ [.list (entries.map edgeValue)]
  refine ⟨after, collectedHeap.length, entries, ?_, ?_, ?_, ?_, ?_⟩
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    exact Evaluates.call (.cons collectedSource .nil)
      (dedup_edges collectedHeap heap.length collected collectedEdges)
  · exact dedup_edges_represents collectedHeap heap.length collected collectedEdges
  · exact dedupBy_unique Prod.snd [] collected (by simp)
  · intro pair
    simpa [entries, contents] using dedupBy_keys Prod.snd [] collected pair
  · exact retained.trans ⟨_, rfl⟩

end data.«project-euler-statements».data.py.project_euler_statements.p79
