import data.«project-euler-statements».data.py.project_euler_statements.«p79.collect.nodes.source»
import data.«project-euler-statements».data.py.project_euler_statements.«p79.collect.edges.source»
import data.«project-euler-statements».data.py.project_euler_statements.«p79.topo.source»

/-! The reference builds the node and edge arguments in Python's left-to-right evaluation order. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

def graphArguments : List Expr :=
  [.call (.name "nodes") [.name "checked"], .call (.name "edges") [.name "checked"]]

theorem naive_return_source : (executableBody
    ((findFunctionIn program.body "naive").getD ([], [])).2).getLast? =
    some (.return (.call (.attribute (.constant (.string "")) "join")
      [.call (.name "topo") graphArguments])) := rfl

theorem heap_prefix_lookup (heap after : Mutable.Heap) (retained : heap <+: after)
    (address : Nat) (object : Mutable.Object) (found : heap[address]? = some object) :
    after[address]? = some object := by
  obtain ⟨extra, rfl⟩ := retained
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem graph_arguments (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text)))
    (env : HeapCalls.Env) (getChecked : env "checked" = some (.ref address)) :
    ∃ after edgesAddress entries,
      Evaluates.Arguments program env graphArguments heap
        [.ref (heap.length + 1), .ref edgesAddress] after ∧
      after[heap.length + 1]? = some (.list ((nodeValues attempts).map text)) ∧
      Edges after edgesAddress entries ∧ (entries.map Prod.snd).Nodup ∧
      (∀ pair, pair ∈ entries.map Prod.snd ↔ pair ∈ attemptEdges attempts) ∧
      heap <+: after := by
  let middle := heap ++ [.list ((attemptCharacters attempts).map text),
    .list ((nodeValues attempts).map text)]
  have initial : heap <+: middle := ⟨_, rfl⟩
  have input := heap_prefix_lookup heap middle initial address _ found
  obtain ⟨after, edgesAddress, entries, executed, edges, unique, contents, retained⟩ :=
    edges_result middle address attempts input
  refine ⟨after, edgesAddress, entries, ?_, ?_, edges, unique, contents, initial.trans retained⟩
  · exact .cons (Evaluates.call (.cons (Evaluates.lookup getChecked) .nil)
      (nodes_result heap address attempts found))
        (.cons (Evaluates.call (.cons (Evaluates.lookup getChecked) .nil) executed) .nil)
  · apply heap_prefix_lookup middle after retained
    simp [middle]

def tripleText (triple : Char × Char × Char) : String :=
  String.ofList [triple.1, triple.2.1, triple.2.2]

def tripleSymbols (triple : Char × Char × Char) : String × String × String :=
  (character triple.1, character triple.2.1, character triple.2.2)

/-- The reference's extra first-to-third edge is redundant, including cyclic observations. -/
theorem reference_order_adjacent (triples : List (Char × Char × Char)) :
    order (nodeValues (triples.map tripleText)) (attemptEdges (triples.map tripleText)) =
      order (nodeValues (triples.map tripleText)) (adjacentEdges (triples.map tripleSymbols)) := by
  have pairs : attemptEdges (triples.map tripleText) =
      expandedEdges (triples.map tripleSymbols) := by
    simp [attemptEdges, observationPairs, expandedEdges, tripleText, tripleSymbols,
      List.flatMap_map]
  rw [pairs]
  apply order_expansion
  intro symbols member
  obtain ⟨triple, present, rfl⟩ := List.mem_map.mp member
  have characterPresent (c : Char) (position : c ∈ [triple.1, triple.2.1, triple.2.2]) :
      character c ∈ nodeValues (triples.map tripleText) := by
    apply (node_values_mem _ _).mpr
    refine ⟨tripleText triple, List.mem_map.mpr ⟨triple, present, rfl⟩, c, ?_, rfl⟩
    simpa [tripleText] using position
  exact ⟨characterPresent triple.1 (by simp), characterPresent triple.2.1 (by simp),
    characterPresent triple.2.2 (by simp)⟩

end data.«project-euler-statements».data.py.project_euler_statements.p79
