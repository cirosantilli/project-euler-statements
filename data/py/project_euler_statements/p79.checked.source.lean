import data.«project-euler-statements».data.py.project_euler_statements.«p79.graph.source»

/-! The reference's final expression builds the graph, orders it, and joins its characters. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TopologicalOrder
set_option Elab.async false

def checkedExpression : Expr := .call (.attribute (.constant (.string "")) "join")
  [.call (.name "topo") graphArguments]

def checkedOutcome (attempts : List String) : Except ExceptionObject Mutable.Value :=
  match order (nodeValues attempts) (attemptEdges attempts) with
  | none => .error cycleException
  | some output => .ok (text (String.intercalate "" output))

theorem checked_expression_source : (executableBody
    ((findFunctionIn program.body "naive").getD ([], [])).2).getLast? =
      some (.return checkedExpression) := naive_return_source

theorem checked_expression_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text)))
    (env : HeapCalls.Env) (getChecked : env "checked" = some (.ref address)) :
    ∃ after, SourceResult (.expr checkedExpression env) heap (checkedOutcome attempts) after ∧
      heap <+: after := by
  obtain ⟨middle, edgeAddress, entries, arguments, nodesFound, edges, _, contents, retained⟩ :=
    graph_arguments heap address attempts found env getChecked
  obtain ⟨after, output, called, outputFound, agrees, untouched⟩ :=
    reference_call_context middle (heap.length + 1) edgeAddress (nodeValues attempts) entries
      nodesFound edges (node_values_unique attempts)
  have sameOrder : order (nodeValues attempts) (entries.map Prod.snd) =
      order (nodeValues attempts) (attemptEdges attempts) :=
    order_edges_congr _ _ _ contents
  have evaluated := source_call env "topo" graphArguments heap middle after
    [.ref (heap.length + 1), .ref edgeAddress]
    (referenceOutcome (middle.length + 1) (order (nodeValues attempts) (attemptEdges attempts)))
    arguments (by simpa only [sameOrder] using called)
  refine ⟨after, ?_, retained.trans ?_⟩
  · cases ordered : order (nodeValues attempts) (attemptEdges attempts) with
    | none =>
        simp only [checkedOutcome, ordered]
        intro anchors stack
        have failed := evaluated anchors
          (.arguments (.join "") [] [] env :: stack)
        simp only [ordered, referenceOutcome] at failed
        refine Finishes.next rfl (Finishes.next rfl ?_)
        exact .next (by simp [HeapCalls.step, run, bindMethod, argumentsState]) failed
    | some result =>
        have listFound : after[middle.length + 1]? = some (.list (result.map text)) := by
          rw [agrees result (sameOrder.trans ordered)] at outputFound
          exact outputFound
        have successful : Evaluates program env (.call (.name "topo") graphArguments)
            heap (.ref (middle.length + 1)) after := by
          simpa only [ordered, referenceOutcome] using evaluated
        have joined := Evaluates.join (module := program) (globals := [])
          Evaluates.constant (.cons successful .nil)
          (primitive_join_list after (middle.length + 1) "" result listFound)
          (by intros; contradiction)
        simpa only [checkedOutcome, ordered] using joined
  · apply List.prefix_iff_getElem?.mpr
    intro index bounded
    simpa only [List.getElem?_eq_getElem bounded] using untouched index bounded

theorem checked_return_result (heap : Mutable.Heap) (address : Nat) (attempts : List String)
    (found : heap[address]? = some (.list (attempts.map text)))
    (env : HeapCalls.Env) (getChecked : env "checked" = some (.ref address)) :
    ∃ after, SourceResult (.block [.return checkedExpression] env) heap
      (checkedOutcome attempts) after ∧ heap <+: after := by
  obtain ⟨after, evaluated, retained⟩ := checked_expression_result heap address attempts found
    env getChecked
  exact ⟨after, SourceResult.before _ _ heap heap after _
    (fun _ _ => .next rfl .refl) evaluated, retained⟩

end data.«project-euler-statements».data.py.project_euler_statements.p79
