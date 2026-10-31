import data.«project-euler-statements».data.py.project_euler_statements.«p79.nodes.source»
import data.«project-euler-statements».data.py.project_euler_statements.«p79.remove.source»

/-! A successful reference iteration emits the least ready node and removes its constraints. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

structure TopoRoots where
  nodes : Nat
  edges : Nat
  output : Nat

structure TopoState (roots : TopoRoots) (nodes : List String) (entries : List Edge)
    (output : List String) (heap : Mutable.Heap) : Prop where
  nodesFound : heap[roots.nodes]? = some (.list (nodes.map text))
  edges : Edges heap roots.edges entries
  outputFound : heap[roots.output]? = some (.list (output.map text))
  nodesOutput : roots.nodes ≠ roots.output
  edgesOutput : roots.edges ≠ roots.output
  unique : nodes.Nodup
  sorted : nodes.Pairwise (· ≤ ·)

structure TopoBindings (roots : TopoRoots) (env : HeapCalls.Env) : Prop where
  nodes : env "ns" = some (.ref roots.nodes)
  edges : env "es" = some (.ref roots.edges)
  output : env "out" = some (.ref roots.output)

def cycleBody : List Stmt :=
  [.raise (some (.call (.name "ValueError")
    [.constant (.string "Constraints contain a cycle; no valid passcode exists.")]))]

def referenceStep : List Stmt :=
  [.assign [.name "found"] nextReady,
   .ifThen (.builtinCall .identity [.name "found", .constant .none]) cycleBody [],
   .expr (.call (.attribute (.name "out") "append") [.name "found"]),
   .assign [.name "ns"] nodeFilter,
   .assign [.name "es"] (.call (.name "remove_node") [.name "found", .name "es"])]

theorem reference_step_source : topoCode =
    [.assign [.name "ns"] (.builtinCall .sorted [.name "ns"]),
     .assign [.name "out"] (.list []),
     .whileDo (.name "ns") referenceStep [], .return (.name "out")] := rfl

def afterEmit (heap : Mutable.Heap) (roots : TopoRoots) (output : List String) (node : String) :=
  heap.set roots.output (.list ((output ++ [node]).map text))

def afterStep (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (node : String) : Mutable.Heap :=
  afterEmit heap roots output node ++
    [.list ((nodes.filter (fun item => decide (item ≠ node))).map text),
     .list ((entries.filter (retain node)).map edgeValue)]

def nextRoots (heap : Mutable.Heap) (roots : TopoRoots) : TopoRoots :=
  ⟨heap.length, heap.length + 1, roots.output⟩

def nextTopoEnv (heap : Mutable.Heap) (env : HeapCalls.Env) (node : String) : HeapCalls.Env :=
  setLocal (setLocal (setLocal env "found" (text node)) "ns" (.ref heap.length))
    "es" (.ref (heap.length + 1))

theorem output_write_edges (heap : Mutable.Heap) (roots : TopoRoots) (entries : List Edge)
    (output : List String) (node : String) (edges : Edges heap roots.edges entries)
    (found : heap[roots.output]? = some (.list (output.map text)))
    (distinct : roots.edges ≠ roots.output) :
    Edges (afterEmit heap roots output node) roots.edges entries := by
  constructor
  · simpa [afterEmit, List.getElem?_set, Ne.symm distinct] using edges.found
  · intro entry member
    have stored := edges.stored entry member
    have different : roots.output ≠ entry.1 := by
      intro same
      change heap[entry.1]? = _ at stored
      rw [← same, found] at stored
      cases stored
    simpa [Stored, afterEmit, List.getElem?_set, different] using stored

theorem step_result (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (state : TopoState roots nodes entries output heap)
    (env : HeapCalls.Env) (bindings : TopoBindings roots env) (node : String)
    (selected : choose nodes (entries.map Prod.snd) = some node) :
    BlockContinues program env referenceStep heap (nextTopoEnv heap env node)
      (afterStep heap roots nodes entries output node) := by
  let chosen := setLocal env "found" (text node)
  let emitted := afterEmit heap roots output node
  let filtered := emitted ++ [.list ((nodes.filter (fun item => decide (item ≠ node))).map text)]
  have choice : Evaluates program env nextReady heap (text node) heap := by
    simpa only [selected, Option.map_some, Option.getD_some] using
      next_ready_choose heap roots.nodes roots.edges nodes entries state.nodesFound state.edges
        state.sorted env bindings.nodes bindings.edges
  have chooseStep : BlockContinues program env [.assign [.name "found"] nextReady]
      heap chosen heap := BlockContinues.assign choice
  have guard : BlockContinues program chosen
      [.ifThen (.builtinCall .identity [.name "found", .constant .none]) cycleBody []]
      heap chosen heap := by
    apply BlockContinues.branch (flag := false) (value := .scalar (.bool false))
      (Evaluates.builtin (values := [text node, .scalar .none])
        (.cons (Evaluates.lookup (by simp [chosen, setLocal])) (.cons Evaluates.constant .nil)) ?_)
      rfl .nil
    rfl
  have emittedStep : BlockContinues program chosen
      [.expr (.call (.attribute (.name "out") "append") [.name "found"])]
      heap chosen emitted := by
    apply BlockContinues.discard
    simpa [emitted, afterEmit, List.map_append] using
      Evaluates.append (module := program)
        (Evaluates.lookup (name := "out")
          (by simpa [chosen, setLocal] using bindings.output)) state.outputFound
        (Evaluates.lookup (name := "found") (by simp [chosen, setLocal])) state.outputFound
  have nodesFound : emitted[roots.nodes]? = some (.list (nodes.map text)) := by
    simpa [emitted, afterEmit, List.getElem?_set, Ne.symm state.nodesOutput] using state.nodesFound
  have edges := output_write_edges heap roots entries output node state.edges
    state.outputFound state.edgesOutput
  have filteredStep : BlockContinues program chosen [.assign [.name "ns"] nodeFilter]
      emitted (setLocal chosen "ns" (.ref heap.length)) filtered := by
    have evaluated := node_filter_result emitted roots.nodes nodes nodesFound chosen node
      (by simpa [chosen, setLocal] using bindings.nodes) (by simp [chosen, setLocal])
    simpa [filtered, emitted, afterEmit] using BlockContinues.assign (name := "ns") evaluated
  have removedStep : BlockContinues program (setLocal chosen "ns" (.ref heap.length))
      [.assign [.name "es"] (.call (.name "remove_node") [.name "found", .name "es"])]
      filtered (nextTopoEnv heap env node) (afterStep heap roots nodes entries output node) := by
    have called := Evaluates.call (env := setLocal chosen "ns" (.ref heap.length))
      (.cons (Evaluates.lookup (name := "found") (by simp [chosen, setLocal]))
        (.cons (Evaluates.lookup (name := "es")
          (by simpa [chosen, setLocal] using bindings.edges)) .nil))
      (remove_result filtered roots.edges entries (edges.append emitted _ roots.edges entries) node)
    simpa [nextTopoEnv, chosen, filtered, emitted, afterEmit, afterStep, List.append_assoc] using
      BlockContinues.assign (name := "es") called
  exact ((chooseStep.append guard).append emittedStep).append
    (filteredStep.append removedStep)

theorem step_state (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (state : TopoState roots nodes entries output heap)
    (node : String) :
    TopoState (nextRoots heap roots) (nodes.filter (fun item => decide (item ≠ node)))
      (entries.filter (retain node)) (output ++ [node])
      (afterStep heap roots nodes entries output node) := by
  have bounded : roots.output < heap.length :=
    (List.getElem?_eq_some_iff.mp state.outputFound).1
  have edges := output_write_edges heap roots entries output node state.edges
    state.outputFound state.edgesOutput
  constructor
  · simp [nextRoots, afterStep, afterEmit]
  · constructor
    · simp [nextRoots, afterStep, afterEmit]
    · intro edge member
      exact (edges.stored edge (List.mem_filter.mp member).1).append _ _ edge
  · simp [nextRoots, afterStep, afterEmit, List.getElem?_append_left, bounded]
  · simp only [nextRoots]; omega
  · simp only [nextRoots]; omega
  · exact state.unique.filter _
  · exact node_filter_sorted nodes node state.sorted

theorem step_bindings (heap : Mutable.Heap) (roots : TopoRoots) (env : HeapCalls.Env)
    (bindings : TopoBindings roots env) (node : String) :
    TopoBindings (nextRoots heap roots) (nextTopoEnv heap env node) := by
  constructor
  · simp [nextRoots, nextTopoEnv, setLocal]
  · simp [nextRoots, nextTopoEnv, setLocal]
  · simpa [nextRoots, nextTopoEnv, setLocal] using bindings.output

end data.«project-euler-statements».data.py.project_euler_statements.p79
