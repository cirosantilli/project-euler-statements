import data.«project-euler-statements».data.py.project_euler_statements.«p79.collect.refs.source»
import data.«project-euler-statements».data.py.project_euler_statements.«p79.observation.source»

/-! Each edge iteration allocates its pairs and appends their references to the collector. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def observationPairs (s : String) : List (String × String) := match s.toList with
  | a :: b :: c :: _ => [(character a, character b), (character b, character c),
      (character a, character c)]
  | _ => []

theorem observation_any (heap : Mutable.Heap) (s : String) :
    ∃ extra entries address,
      ReturnsValue program "edges_from" [text s] heap (.ref address) (heap ++ extra) ∧
      Edges (heap ++ extra) address entries ∧ entries.map Prod.snd = observationPairs s ∧
      heap.length ≤ address := by
  have small (short : s.length < 3) (empty : observationPairs s = []) :
      ∃ extra entries address,
        ReturnsValue program "edges_from" [text s] heap (.ref address) (heap ++ extra) ∧
        Edges (heap ++ extra) address entries ∧ entries.map Prod.snd = observationPairs s ∧
        heap.length ≤ address := by
    refine ⟨[.list []], [], heap.length, observation_short heap s short, ?_, ?_, le_rfl⟩
    · exact ⟨by simp, by simp⟩
    · simpa using empty.symm
  have size : s.toList.length = s.length := by simp
  rcases chars : s.toList with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
  · exact small (by simp [chars] at size; omega) (by simp [observationPairs, chars])
  · exact small (by simp [chars] at size; omega) (by simp [observationPairs, chars])
  · exact small (by simp [chars] at size; omega) (by simp [observationPairs, chars])
  · refine ⟨_, observationEntries heap.length a b c, heap.length + 3,
      observation_result heap s a b c tail chars, observation_represents heap a b c, ?_, by omega⟩
    simp [observationEntries, observationPairs, chars]

def collectEdgeBody (collector : Nat) : List Stmt :=
  [.forIn (.name "e") (.call (.name "edges_from") [.name "s"])
    [.comprehensionAppend collector (.name "e")] []]

theorem collect_edge_step (heap : Mutable.Heap) (collector : Nat) (collected : List Edge)
    (edges : Edges heap collector collected) (env : HeapCalls.Env) (s : String)
    (getS : env "s" = some (text s)) :
    ∃ after entries finalEnv,
      BlockContinues program env (collectEdgeBody collector) heap finalEnv after ∧
      Edges after collector entries ∧ entries.map Prod.snd = collected.map Prod.snd ++
        observationPairs s ∧ heap.length ≤ after.length ∧
      (∀ address < heap.length, address ≠ collector → after[address]? = heap[address]?) := by
  obtain ⟨extra, added, address, executed, represented, pairs, fresh⟩ := observation_any heap s
  have bounded := (List.getElem?_eq_some_iff.mp edges.found).1
  have separate : address ≠ collector := by omega
  have extended := edges.append heap extra collector collected
  obtain ⟨finalEnv, copied⟩ := collect_refs_loop (heap ++ extra) address collector
    (added.map edgeValue) [] (added.map edgeValue) (collected.map edgeValue)
    represented.found extended.found separate rfl env
  let after := (heap ++ extra).set collector (.list ((collected ++ added).map edgeValue))
  refine ⟨after, collected ++ added, finalEnv, ?_, ?_, ?_, ?_, ?_⟩
  · apply BlockContinues.for_sequence (items := added.map edgeValue)
      (by intro expressions; simp)
      (Evaluates.call (.cons (Evaluates.lookup getS) .nil) executed)
      (by simp [Mutable.sequence, represented.found])
    simpa [after, List.map_append] using copied
  · constructor
    · exact List.getElem?_set_self (by simp; omega)
    · intro entry member
      apply stored_after_list_write (heap ++ extra) collector (collected.map edgeValue)
        _ extended.found entry
      rcases List.mem_append.mp member with old | new
      · exact extended.stored entry old
      · exact represented.stored entry new
  · simp [pairs]
  · simp [after]
  · intro index inside different
    simp [after, Ne.symm different, List.getElem?_append_left, inside]

end data.«project-euler-statements».data.py.project_euler_statements.p79
