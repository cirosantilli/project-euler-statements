import data.«project-euler-statements».data.py.project_euler_statements.«p61.loops.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p61.extend
open FormalSW.PyAst HeapCalls ProjectEulerSolutions
private abbrev program := P61Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)

private theorem empty_result (fuel : Nat) (values : List Int) (nonempty : values ≠ [])
    (heap : Mutable.Heap) (path remainingAddress familiesCell : Nat)
    (pathFound : heap[path]? = some (.list (numbers values))) (remainingFound : heap[remainingAddress]? = some (.list []))
    (globals : Mutable.Globals) :
    ∃ extra, ReturnsValue program "__formalsw_local_naive_extend" [.ref path, .ref remainingAddress, .ref familiesCell]
      heap (number (PolygonalCycleSearch.fullScan PolygonalFamilies.family fuel values [])) (heap ++ extra) globals := by
  have model : PolygonalCycleSearch.fullScan PolygonalFamilies.family fuel values [] =
      (if PolygonalCycleSearch.closed values then values.sum else 0) := by cases fuel <;> rfl
  refine ⟨[], ?_⟩
  rw [model]
  simpa only [List.append_nil] using closed_result values nonempty heap path remainingAddress pathFound remainingFound (.ref familiesCell) globals

/-- The full recursive reference search terminates and returns its exact maximum-search model. -/
theorem search_result (fuel : Nat) (heap : Mutable.Heap) (path remainingAddress familiesCell : Nat) (maxSides : Int)
    (values : List Int) (remaining : List Int)
    (state : SearchState heap path remainingAddress familiesCell maxSides values remaining)
    (nonempty : values ≠ []) (depth : remaining.length ≤ fuel) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "__formalsw_local_naive_extend" [.ref path, .ref remainingAddress, .ref familiesCell]
      heap (number (PolygonalCycleSearch.fullScan PolygonalFamilies.family fuel values remaining)) (heap ++ extra) globals := by
  induction fuel generalizing heap path remainingAddress familiesCell maxSides values remaining with
  | zero =>
      have empty : remaining = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst remaining
      exact empty_result 0 values nonempty heap path remainingAddress familiesCell state.pathFound state.remainingFound globals
  | succ fuel ih =>
      by_cases empty : remaining = []
      · subst remaining
        exact empty_result (fuel + 1) values nonempty heap path remainingAddress familiesCell state.pathFound state.remainingFound globals
      · obtain ⟨last, atEnd⟩ : ∃ last, values.getLast? = some last := by
          cases found : values.getLast? with
          | none => exact False.elim (nonempty (List.getLast?_eq_none_iff.mp found))
          | some last => exact ⟨last, rfl⟩
        have noTypes : remaining.isEmpty = false := by
          cases remaining with
          | nil => exact False.elim (empty rfl)
          | cons _ _ => rfl
        let params := ((findFunctionIn program.body "__formalsw_local_naive_extend").getD ([], [])).1
        let sourceBody := ((findFunctionIn program.body "__formalsw_local_naive_extend").getD ([], [])).2
        let env := functionEnv params sourceBody [.ref path, .ref remainingAddress, .ref familiesCell] globals
        have bound : Bindings env path remainingAddress familiesCell := Bindings.function path remainingAddress familiesCell globals
        let bestEnv := setLocal env "best" (number 0)
        have bestBound : Bindings bestEnv path remainingAddress familiesCell := bound.local "best" _ (by decide)
        let visit := fun kind value => PolygonalCycleSearch.fullScan PolygonalFamilies.family fuel (values ++ [value])
          (remaining.filter (fun other => decide (other ≠ kind)))
        have child : ∀ currentHeap kind unused value,
            SearchState currentHeap path remainingAddress familiesCell maxSides values remaining → kind ∈ remaining →
            currentHeap[unused]? = some (.list (kinds (remaining.filter (fun other => decide (other ≠ kind))))) →
            value ∈ PolygonalFamilies.family kind → value ∉ values →
            ProjectEulerSolutions.PolygonalCycle.links last value = true →
            ∃ extra, ReturnsValue program "__formalsw_local_naive_extend"
              [.ref (currentHeap.length + 1), .ref unused, .ref familiesCell] (childHeap currentHeap values value)
              (number (visit kind value)) (childHeap currentHeap values value ++ extra) globals := by
          intro currentHeap kind unused value ready member unusedFound _ _ _
          have smaller := PolygonalCycleSearch.unused_shorter remaining kind member
          exact ih (childHeap currentHeap values value) (currentHeap.length + 1) unused familiesCell maxSides
            (values ++ [value]) (remaining.filter (fun other => decide (other ≠ kind)))
            (ready.child kind value unused unusedFound) (by simp) (by omega)
        obtain ⟨extra, finalEnv, executed, finalBound, finalBest, frame⟩ :=
          type_loop state bestBound last atEnd 0 rfl visit child
        have model : PolygonalCycleSearch.fullScan PolygonalFamilies.family (fuel + 1) values remaining =
            remaining.foldl (advanceKind values last visit) 0 := by
          rw [PolygonalCycleSearch.fullScan, noTypes]
          simp only [Bool.false_eq_true, if_false, PolygonalCycleSearch.last, atEnd, Option.getD_some]
          congr 1
          funext best kind
          unfold advanceKind
          congr 1
          funext best value
          simp only [advance, ProjectEulerSolutions.PolygonalCycle.links, decide_eq_true_eq, visit]
        refine ⟨extra, ?_⟩
        rw [model]
        apply BlockReturns.function rfl rfl
        change BlockReturns program env code heap _ (heap ++ extra) globals
        have tested : Evaluates program env exhausted heap (flag false) heap globals := by
          apply Evaluates.unary (middle := heap) (finalHeap := heap) (Evaluates.lookup bound.getRemaining)
          simp [HeapCalls.unary, Mutable.truth, state.remainingFound, kinds, noTypes, flag]
        apply BlockReturns.branch (flag := false) tested rfl
        apply BlockReturns.assign Evaluates.constant
        exact BlockContinues.returns executed (BlockReturns.return_value (Evaluates.lookup finalBest))
end data.«project-euler-statements».data.py.project_euler_statements.p61.extend
