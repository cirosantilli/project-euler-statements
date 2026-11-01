import data.«project-euler-statements».data.py.project_euler_statements.«p79.choice.source»

/-! Validation follows the schedule through every finite set, including mixed valid and invalid attempts. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def setValidationLoop (address : Nat) (original remaining : List String) : Stmt :=
  .setStepLoop "attempt" address (original.map Constant.string) (remaining.map Constant.string)
    validationBody []

theorem validated_set (choices : ChoiceSchedule) (used : Nat) (base : Mutable.Heap)
    (address : Nat) (original remaining checked : List String) (env : HeapCalls.Env)
    (found : base[address]? = some (.set (original.map Constant.string)))
    (getChecked : env "checked" = some (.ref base.length)) (anchors : Nat) :
    ∃ after, Finishes (SetCalls.step program anchors choices)
      ⟨⟨.block [setValidationLoop address original remaining, .return checkedExpression] env,
        [], base ++ [.list (checked.map text)]⟩, used⟩
      (.ok ⟨validatedOutcome checked (SetCalls.selectionOrder choices used remaining), [], after, anchors⟩) ∧
      base <+: after := by
  have retained : (base ++ [.list (checked.map text)])[address]? =
      some (.set (original.map Constant.string)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  cases remaining with
  | nil =>
      obtain ⟨after, returned, saved⟩ := checked_return_result
        (base ++ [.list (checked.map text)]) base.length checked (by simp) env getChecked
      refine ⟨after, ?_, (List.prefix_append _ _).trans saved⟩
      simp only [SetCalls.selectionOrder, validatedOutcome]
      apply Finishes.next (following :=
        ⟨⟨.block [.return checkedExpression] env, [], base ++ [.list (checked.map text)]⟩, used⟩)
      · simp [SetCalls.step, step, SetCalls.iteratorStep, setValidationLoop, retained]
      · exact SetCalls.finishes_of_heap (SourceResult.finishes _ _ _ _ returned anchors) choices used
  | cons head tail =>
      let index := choices used % (head :: tail).length
      have bounded : index < (head :: tail).length := Nat.mod_lt _ (by simp)
      let s := (head :: tail)[index]
      let rest := (head :: tail).eraseIdx index
      let bound := setLocal env "attempt" (text s)
      have boundChecked : bound "checked" = some (.ref base.length) := by
        simpa [bound, setLocal] using getChecked
      have boundAttempt : bound "attempt" = some (text s) := by simp [bound, setLocal]
      have selected : ((head :: tail).map Constant.string)[index]? = some (.string s) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem bounded]
        rfl
      have control : Calls.loopControl validationBody = false := rfl
      have entered : SetCalls.step program anchors choices
          ⟨⟨.block [setValidationLoop address original (head :: tail), .return checkedExpression] env,
            [], base ++ [.list (checked.map text)]⟩, used⟩ =
          .next ⟨⟨.block (validationBody ++ [setValidationLoop address original rest,
            .return checkedExpression]) bound, [], base ++ [.list (checked.map text)]⟩, used + 1⟩ := by
        simpa only [setValidationLoop, Calls.loopContinuation, control, Bool.false_eq_true,
          ↓reduceIte, List.eraseIdx_map, List.singleton_append, rest, bound, text] using
          SetCalls.select_item_mod program choices anchors used address index
            (base ++ [.list (checked.map text)]) (original.map Constant.string)
            ((head :: tail).map Constant.string) (.string s) env "attempt" validationBody []
            [.return checkedExpression] [] retained selected (by simp [index])
      rw [SetCalls.selectionOrder]
      change ∃ after, Finishes (SetCalls.step program anchors choices)
        ⟨⟨.block [setValidationLoop address original (head :: tail), .return checkedExpression] env,
          [], base ++ [.list (checked.map text)]⟩, used⟩
        (.ok ⟨validatedOutcome checked (s :: SetCalls.selectionOrder choices (used + 1) rest),
          [], after, anchors⟩) ∧ base <+: after
      by_cases valid : s.length = 3 ∧ Strings.isDigit s = true
      · simp only [validatedOutcome, if_pos valid]
        obtain ⟨after, completed, saved⟩ := validated_set choices (used + 1) base address original rest
          (checked ++ [s]) bound found boundChecked anchors
        refine ⟨after, .next entered ?_, saved⟩
        exact (SetCalls.Reaches.of_heap
          (accepted_attempt base checked bound s boundChecked boundAttempt valid.1 valid.2
            [setValidationLoop address original rest, .return checkedExpression] anchors [])
          choices (used + 1)).finishes completed
      · simp only [validatedOutcome, if_neg valid]
        refine ⟨base ++ [.list (checked.map text)], .next entered ?_, List.prefix_append _ _⟩
        apply SetCalls.finishes_of_heap (rejected_attempt bound _ s boundAttempt ?_ _ anchors [])
        by_cases length : s.length = 3
        · exact Or.inr (by simpa [length] using valid)
        · exact Or.inl length
termination_by remaining.length
decreasing_by
  rw [List.length_eraseIdx_of_lt bounded]
  simp

theorem naive_set_finishes (choices : ChoiceSchedule) (base : Mutable.Heap)
    (address : Nat) (attempts : List String)
    (found : base[address]? = some (.set (attempts.map Constant.string))) :
    ∃ after, ((SetCalls.call program "naive" [.ref address] base).run choices).Finishes
      ⟨validatedOutcome [] (SetCalls.selectionOrder choices 0 attempts), [], after, base.length⟩ ∧
      base <+: after := by
  let env := setValidationEnv (.ref address)
  let bound := setLocal env "checked" (.ref base.length)
  let heap := base ++ [Mutable.Object.list []]
  obtain ⟨after, completed, saved⟩ := validated_set choices 0 base address attempts attempts []
    bound found (by simp [bound, setLocal]) base.length
  refine ⟨after, ?_, saved⟩
  change Finishes (SetCalls.step program base.length choices)
    ⟨⟨.operation (.call "naive") [.ref address], [], base⟩, 0⟩ _
  apply (SetCalls.Reaches.of_heap
    (show HeapCalls.Reaches program base.length
      ⟨.operation (.call "naive") [.ref address], [], base⟩ ⟨.block naiveCode env, [], base⟩
      from .next rfl .refl) choices 0).finishes
  rw [naive_source]
  have allocated : BlockContinues program env
      [.annAssign (.name "checked") (.subscript (.name "list") (.name "str")) (some (.list []))]
      base bound heap := BlockContinues.annAssign (Evaluates.list .nil)
  apply (SetCalls.Reaches.of_heap (allocated _ base.length []) choices 0).finishes
  apply (SetCalls.for_set_name program choices base.length 0 address heap
    (attempts.map Constant.string) bound "attempt" "attempts" validationBody []
    [.return checkedExpression] [] (by rfl) ?_).finishes completed
  simpa only [heap, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found

/-- Reordering validated attempts changes neither their graph constraints nor the least ordering. -/
theorem checkedOutcome_perm (left right : List String) (permutation : left.Perm right) :
    checkedOutcome left = checkedOutcome right := by
  have characters : (attemptCharacters left).Perm (attemptCharacters right) :=
    permutation.flatMap_right (fun (s : String) => s.toList.map String.singleton)
  have nodes : (nodeValues left).Perm (nodeValues right) := by
    apply (List.perm_ext_iff_of_nodup (node_values_unique left) (node_values_unique right)).mpr
    intro value
    have contents (attempts : List String) : value ∈ nodeValues attempts ↔ value ∈ attemptCharacters attempts := by
      simpa [nodeValues] using dedupBy_keys id [] (attemptCharacters attempts) value
    exact (contents left).trans (characters.mem_iff.trans (contents right).symm)
  have edges : (attemptEdges left).Perm (attemptEdges right) :=
    permutation.flatMap_right observationPairs
  unfold checkedOutcome
  rw [ProjectEulerStatements.TopologicalOrder.order_nodes_perm _ _ _ nodes,
    ProjectEulerStatements.TopologicalOrder.order_edges_congr _ _ _ (fun _ => edges.mem_iff)]

end data.«project-euler-statements».data.py.project_euler_statements.p79
