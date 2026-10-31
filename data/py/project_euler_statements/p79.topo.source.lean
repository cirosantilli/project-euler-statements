import data.«project-euler-statements».data.py.project_euler_statements.«p79.loop.source»
import ProjectEulerStatements.Lib.PrecedenceTriples

/-! The reference topological sort returns the least ordering without mutating its inputs. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

def preparedHeap (heap : Mutable.Heap) (nodes : List String) : Mutable.Heap :=
  heap ++ [.list ((ScalarSort.strings nodes).map text), .list []]

def preparedRoots (heap : Mutable.Heap) (edgesAddress : Nat) : TopoRoots :=
  ⟨heap.length, edgesAddress, heap.length + 1⟩

def preparedEnv (heap : Mutable.Heap) (env : HeapCalls.Env) : HeapCalls.Env :=
  setLocal (setLocal env "ns" (.ref heap.length)) "out" (.ref (heap.length + 1))

theorem initialize_reference (heap : Mutable.Heap) (address : Nat) (nodes : List String)
    (found : heap[address]? = some (.list (nodes.map text)))
    (env : HeapCalls.Env) (getNodes : env "ns" = some (.ref address)) :
    BlockContinues program env (topoCode.take 2) heap (preparedEnv heap env)
      (preparedHeap heap nodes) := by
  have sorted := BlockContinues.assign (name := "ns")
    (sort_nodes_result heap address nodes found env getNodes)
  have output := BlockContinues.assign (name := "out")
    (Evaluates.list (module := program) (globals := [])
      (env := setLocal env "ns" (.ref heap.length))
      (heap := heap ++ [.list ((ScalarSort.strings nodes).map text)]) .nil)
  simpa [preparedHeap, preparedEnv, List.append_assoc] using sorted.append output

theorem prepared_state (heap : Mutable.Heap) (edgesAddress : Nat) (nodes : List String)
    (entries : List Edge) (edges : Edges heap edgesAddress entries) (unique : nodes.Nodup) :
    TopoState (preparedRoots heap edgesAddress) (ScalarSort.strings nodes) entries []
      (preparedHeap heap nodes) := by
  have bounded := (List.getElem?_eq_some_iff.mp edges.found).1
  constructor
  · simp [preparedHeap, preparedRoots]
  · exact edges.append heap _ edgesAddress entries
  · simp [preparedHeap, preparedRoots]
  · simp [preparedRoots]
  · simp only [preparedRoots]; omega
  · exact (ScalarSort.strings_perm nodes).nodup_iff.mpr unique
  · exact ProjectEulerStatements.StringSorting.strings_ordered nodes

theorem prepared_bindings (heap : Mutable.Heap) (edgesAddress : Nat) (env : HeapCalls.Env)
    (getEdges : env "es" = some (.ref edgesAddress)) :
    TopoBindings (preparedRoots heap edgesAddress) (preparedEnv heap env) := by
  constructor
  · simp [preparedRoots, preparedEnv, setLocal]
  · simpa [preparedRoots, preparedEnv, setLocal] using getEdges
  · simp [preparedRoots, preparedEnv, setLocal]

/-- Node enumeration order is irrelevant; every original heap cell is preserved. -/
theorem reference_body_context (heap : Mutable.Heap) (nodesAddress edgesAddress : Nat)
    (nodes : List String) (entries : List Edge)
    (found : heap[nodesAddress]? = some (.list (nodes.map text)))
    (edges : Edges heap edgesAddress entries) (unique : nodes.Nodup)
    (env : HeapCalls.Env) (getNodes : env "ns" = some (.ref nodesAddress))
    (getEdges : env "es" = some (.ref edgesAddress)) :
    ∃ after finalOutput,
      SourceResult (.block topoCode env) heap
        (referenceOutcome (heap.length + 1) (order nodes (entries.map Prod.snd))) after ∧
      after[heap.length + 1]? = some (.list (finalOutput.map text)) ∧
      (∀ result, order nodes (entries.map Prod.snd) = some result → finalOutput = result) ∧
      (∀ address < heap.length, after[address]? = heap[address]?) := by
  obtain ⟨after, finalOutput, completed, outputFound, agrees, untouched⟩ :=
    reference_loop_context (preparedHeap heap nodes) (preparedRoots heap edgesAddress)
      (ScalarSort.strings nodes) entries []
      (prepared_state heap edgesAddress nodes entries edges unique)
      (preparedEnv heap env) (prepared_bindings heap edgesAddress env getEdges)
  have same : order (ScalarSort.strings nodes) (entries.map Prod.snd) =
      order nodes (entries.map Prod.snd) :=
    order_nodes_perm _ _ _ (ScalarSort.strings_perm nodes)
  refine ⟨after, finalOutput, ?_, outputFound, ?_, ?_⟩
  · have combined := SourceResult.before _ _ heap (preparedHeap heap nodes) after _
      (fun anchors stack => initialize_reference heap nodesAddress nodes found env getNodes
        [referenceLoop, .return (.name "out")] anchors stack) completed
    simpa only [same] using combined
  · intro result ordered
    simpa only [List.nil_append] using agrees result (same.trans ordered)
  · intro address bounded
    have saved := untouched address (by simp [preparedHeap]; omega)
      (by simp [preparedRoots]; omega)
    simpa [preparedHeap, List.getElem?_append_left, bounded] using saved

theorem reference_body_result (heap : Mutable.Heap) (nodesAddress edgesAddress : Nat)
    (nodes : List String) (entries : List Edge)
    (found : heap[nodesAddress]? = some (.list (nodes.map text)))
    (edges : Edges heap edgesAddress entries) (unique : nodes.Nodup)
    (env : HeapCalls.Env) (getNodes : env "ns" = some (.ref nodesAddress))
    (getEdges : env "es" = some (.ref edgesAddress)) (anchors : Nat) :
    ∃ after finalOutput,
      Finishes (HeapCalls.step program anchors) ⟨.block topoCode env, [], heap⟩
        (.ok ⟨referenceOutcome (heap.length + 1) (order nodes (entries.map Prod.snd)), [],
          after, anchors⟩) ∧
      after[heap.length + 1]? = some (.list (finalOutput.map text)) ∧
      (∀ result, order nodes (entries.map Prod.snd) = some result → finalOutput = result) ∧
      (∀ address < heap.length, after[address]? = heap[address]?) := by
  obtain ⟨after, finalOutput, result, contents, agrees, preserved⟩ :=
    reference_body_context heap nodesAddress edgesAddress nodes entries found edges unique
      env getNodes getEdges
  exact ⟨after, finalOutput, SourceResult.finishes _ _ _ _ result anchors,
    contents, agrees, preserved⟩

/-- The call result composes with an enclosing expression or statement in either outcome. -/
theorem reference_call_context (heap : Mutable.Heap) (nodesAddress edgesAddress : Nat)
    (nodes : List String) (entries : List Edge)
    (found : heap[nodesAddress]? = some (.list (nodes.map text)))
    (edges : Edges heap edgesAddress entries) (unique : nodes.Nodup) :
    ∃ after finalOutput,
      SourceResult (.operation (.call "topo") [.ref nodesAddress, .ref edgesAddress]) heap
        (referenceOutcome (heap.length + 1) (order nodes (entries.map Prod.snd))) after ∧
      after[heap.length + 1]? = some (.list (finalOutput.map text)) ∧
      (∀ result, order nodes (entries.map Prod.snd) = some result → finalOutput = result) ∧
      (∀ address < heap.length, after[address]? = heap[address]?) := by
  let source := (findFunctionIn program.body "topo").getD ([], [])
  let env := functionEnv source.1 source.2 [.ref nodesAddress, .ref edgesAddress] []
  obtain ⟨after, output, completed, contents, agrees, preserved⟩ :=
    reference_body_context heap nodesAddress edgesAddress nodes entries found edges unique
      env rfl rfl
  refine ⟨after, output, ?_, contents, agrees, preserved⟩
  exact SourceResult.before _ _ heap heap after _ (fun _ _ => .next rfl .refl) completed

/-- This is the source function call, including normal and exceptional completion. -/
theorem reference_call_result (heap : Mutable.Heap) (nodesAddress edgesAddress : Nat)
    (nodes : List String) (entries : List Edge)
    (found : heap[nodesAddress]? = some (.list (nodes.map text)))
    (edges : Edges heap edgesAddress entries) (unique : nodes.Nodup) :
    ∃ after finalOutput,
      (HeapCalls.call program "topo" [.ref nodesAddress, .ref edgesAddress] heap).Finishes
        ⟨referenceOutcome (heap.length + 1) (order nodes (entries.map Prod.snd)), [],
          after, heap.length⟩ ∧
      after[heap.length + 1]? = some (.list (finalOutput.map text)) ∧
      (∀ result, order nodes (entries.map Prod.snd) = some result → finalOutput = result) ∧
      (∀ address < heap.length, after[address]? = heap[address]?) := by
  let source := (findFunctionIn program.body "topo").getD ([], [])
  let env := functionEnv source.1 source.2 [.ref nodesAddress, .ref edgesAddress] []
  obtain ⟨after, output, completed, contents, agrees, preserved⟩ :=
    reference_body_result heap nodesAddress edgesAddress nodes entries found edges unique
      env rfl rfl heap.length
  exact ⟨after, output, .next rfl completed, contents, agrees, preserved⟩

end data.«project-euler-statements».data.py.project_euler_statements.p79
