import data.«project-euler-statements».data.py.project_euler_statements.«p79.step.source»

/-! The reference loop terminates with the greedy ordering or its exact cycle exception. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

def referenceLoop : Stmt := .whileDo (.name "ns") referenceStep []

def cycleException : ExceptionObject :=
  { typeName := "ValueError",
    args := [.string "Constraints contain a cycle; no valid passcode exists."] }

def referenceOutcome (address : Nat) : Option (List String) → Except ExceptionObject Mutable.Value
  | none => .error cycleException
  | some _ => .ok (.ref address)

theorem enter_reference_loop (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (state : TopoState roots nodes entries output heap)
    (env : HeapCalls.Env) (bindings : TopoBindings roots env) (nonempty : nodes ≠ [])
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) :
    Reaches program anchors ⟨.block (referenceLoop :: following) env, stack, heap⟩
      ⟨.block (referenceStep ++ referenceLoop :: following) env, stack, heap⟩ := by
  apply Reaches.next rfl
  apply ((Evaluates.lookup (module := program) (heap := heap) bindings.nodes) anchors _).trans
  exact .next (by
    simp [HeapCalls.step, run, Mutable.truth, state.nodesFound, nonempty, referenceLoop,
      referenceStep, cycleBody, Calls.loopContinuation, Calls.loopControl,
      Calls.loopControlStmt]) .refl

theorem raise_cycle (heap : Mutable.Heap) (env : HeapCalls.Env) (following : List Stmt)
    (anchors : Nat) :
    Finishes (HeapCalls.step program anchors) ⟨.block (cycleBody ++ following) env, [], heap⟩
      (.ok ⟨.error cycleException, [], heap, anchors⟩) := by
  refine Finishes.next (following := argumentsState (.raiseException "ValueError") env []
    [.constant (.string "Constraints contain a cycle; no valid passcode exists.")] [] heap) rfl ?_
  apply (Evaluates.arguments_reach
    (.cons (Evaluates.constant (module := program) (env := env)) .nil)
    (.raiseException "ValueError") [] anchors []).finishes
  exact .done (by
    simp [HeapCalls.step, result, run, primitive, done, cycleException, protectGenerator,
      Calls.generatorException])

theorem no_choice_cycle (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (state : TopoState roots nodes entries output heap)
    (env : HeapCalls.Env) (bindings : TopoBindings roots env)
    (selected : choose nodes (entries.map Prod.snd) = none)
    (following : List Stmt) (anchors : Nat) :
    Finishes (HeapCalls.step program anchors)
      ⟨.block (referenceStep ++ following) env, [], heap⟩
      (.ok ⟨.error cycleException, [], heap, anchors⟩) := by
  let chosen := setLocal env "found" (.scalar .none)
  have choice : Evaluates program env nextReady heap (.scalar .none) heap := by
    simpa only [selected, Option.map_none, Option.getD_none] using
      next_ready_choose heap roots.nodes roots.edges nodes entries state.nodesFound state.edges
        state.sorted env bindings.nodes bindings.edges
  have assigned := BlockContinues.assign (name := "found") choice
  apply (assigned (referenceStep.drop 1 ++ following) anchors []).finishes
  have test : Evaluates program chosen (.builtinCall .identity [.name "found", .constant .none])
      heap (.scalar (.bool true)) heap :=
    Evaluates.builtin (values := [.scalar .none, .scalar .none])
      (.cons (Evaluates.lookup (by simp [chosen, setLocal]))
      (.cons Evaluates.constant .nil)) rfl
  refine Finishes.next rfl ((test anchors _).finishes ?_)
  exact .next (by simp [HeapCalls.step, run, Mutable.truth, scalarTruth, referenceStep, chosen])
    (raise_cycle heap chosen (referenceStep.drop 2 ++ following) anchors)

theorem step_untouched (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (node : String) (address : Nat)
    (bounded : address < heap.length) (different : address ≠ roots.output) :
    (afterStep heap roots nodes entries output node)[address]? = heap[address]? := by
  simp [afterStep, afterEmit, List.getElem?_append_left, bounded, Ne.symm different]

/-- The measure is the actual remaining node count, with no imposed search bound. -/
theorem reference_loop_result (heap : Mutable.Heap) (roots : TopoRoots) (nodes : List String)
    (entries : List Edge) (output : List String) (state : TopoState roots nodes entries output heap)
    (env : HeapCalls.Env) (bindings : TopoBindings roots env) (anchors : Nat) :
    ∃ after finalOutput,
      Finishes (HeapCalls.step program anchors)
        ⟨.block [referenceLoop, .return (.name "out")] env, [], heap⟩
        (.ok ⟨referenceOutcome roots.output (order nodes (entries.map Prod.snd)), [],
          after, anchors⟩) ∧
      after[roots.output]? = some (.list (finalOutput.map text)) ∧
      (∀ result, order nodes (entries.map Prod.snd) = some result →
        finalOutput = output ++ result) ∧
      (∀ address < heap.length, address ≠ roots.output → after[address]? = heap[address]?) := by
  by_cases empty : nodes = []
  · subst nodes
    have ordered : order ([] : List String) (entries.map Prod.snd) = some [] := by
      rw [order, if_pos rfl]
    refine ⟨heap, output, ?_, state.outputFound, ?_, by intros; rfl⟩
    · have exited := BlockContinues.while_loop (globals := [])
        (body := referenceStep) (otherwise := [])
        (Evaluates.lookup (module := program) (heap := heap) bindings.nodes)
        (show Mutable.truth (.ref roots.nodes) heap = some (.ok false, heap) by
          simp [Mutable.truth, state.nodesFound]) BlockContinues.nil
      have returned := BlockReturns.return_value (globals := []) (rest := [])
        (Evaluates.lookup (module := program) (heap := heap) bindings.output)
      simpa only [ordered, referenceOutcome] using
        (exited [.return (.name "out")] anchors []).finishes
          ((returned anchors []).finishes (.done rfl))
    · intro result same
      have : result = [] := by simpa only [ordered, Option.some.injEq] using same.symm
      simp [this]
  · cases selected : choose nodes (entries.map Prod.snd) with
    | none =>
        have failed : order nodes (entries.map Prod.snd) = none := by
          rw [order, if_neg empty, selected]
        refine ⟨heap, output, ?_, state.outputFound, ?_, by intros; rfl⟩
        · have entered := enter_reference_loop heap roots nodes entries output state env bindings
            empty [.return (.name "out")] anchors []
          simpa only [failed, referenceOutcome] using
            entered.finishes (no_choice_cycle heap roots nodes entries output state env bindings
              selected [referenceLoop, .return (.name "out")] anchors)
        · intro result same
          rw [failed] at same
          contradiction
    | some node =>
        have member := (choose_spec nodes (entries.map Prod.snd) node selected).1
        let remaining := nodes.filter (fun item => decide (item ≠ node))
        let retained := entries.filter (retain node)
        have shorter : remaining.length < nodes.length := by
          rw [show remaining = nodes.erase node from node_filter_erase nodes node state.unique,
            List.length_erase_of_mem member]
          have := List.length_pos_of_mem member
          omega
        let stepped := afterStep heap roots nodes entries output node
        let next := nextRoots heap roots
        let nextEnv := nextTopoEnv heap env node
        have nextState := step_state heap roots nodes entries output state node
        have nextBindings := step_bindings heap roots env bindings node
        obtain ⟨after, finalOutput, finished, found, agrees, untouched⟩ :=
          reference_loop_result stepped next remaining retained (output ++ [node])
            nextState nextEnv nextBindings anchors
        have recurrence : order nodes (entries.map Prod.snd) =
            (order remaining (retained.map Prod.snd)).map (node :: ·) := by
          rw [order, if_neg empty, selected]
          change (order (nodes.erase node) (removeNode node (entries.map Prod.snd))).map _ = _
          rw [show remaining = nodes.erase node from node_filter_erase nodes node state.unique,
            remove_contents]
        have sameOutcome : referenceOutcome roots.output (order nodes (entries.map Prod.snd)) =
            referenceOutcome next.output (order remaining (retained.map Prod.snd)) := by
          rw [recurrence]
          cases order remaining (retained.map Prod.snd) <;> rfl
        refine ⟨after, finalOutput, ?_, found, ?_, ?_⟩
        · rw [sameOutcome]
          apply (enter_reference_loop heap roots nodes entries output state env bindings empty
            [.return (.name "out")] anchors []).finishes
          exact (step_result heap roots nodes entries output state env bindings node selected
            [referenceLoop, .return (.name "out")] anchors []).finishes finished
        · intro result same
          rw [recurrence] at same
          obtain ⟨rest, ordered, rfl⟩ := Option.map_eq_some_iff.mp same
          simpa only [List.append_assoc, List.singleton_append] using agrees rest ordered
        · intro address bounded different
          exact (untouched address (by
            simp only [stepped, afterStep, afterEmit, List.length_append, List.length_set,
              List.length_cons, List.length_nil]
            omega) different).trans
              (step_untouched heap roots nodes entries output node address bounded different)
termination_by nodes.length

end data.«project-euler-statements».data.py.project_euler_statements.p79
