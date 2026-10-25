import data.«project-euler-statements».data.py.project_euler_statements.«p61.arguments.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p61.extend
open FormalSW.PyAst HeapCalls ProjectEulerSolutions
private abbrev program := P61Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)

def advance (values : List Int) (last : Int) (visit : Int → Int) (best value : Int) : Int :=
  if value ∈ values then best else
    if ProjectEulerSolutions.PolygonalCycle.links last value then max best (visit value) else best

/-- The actual candidate loop computes the guarded maximum and retains all child heap effects. -/
theorem candidate_loop (state : SearchState heap path remainingAddress familiesCell maxSides values remaining)
    (bound : Bindings env path remainingAddress familiesCell) (last : Int) (atEnd : values.getLast? = some last)
    (kind : Int) (unused : Nat)
    (unusedFound : heap[unused]? = some (.list (kinds (remaining.filter (fun other => decide (other ≠ kind))))))
    (getUnused : env "unused" = some (.ref unused)) (best : Int) (getBest : env "best" = some (number best))
    (all : List Int) (source : Nat) (found : heap[source]? = some (.list (numbers all))) (visit : Int → Int)
    (child : ∀ currentHeap value, SearchState currentHeap path remainingAddress familiesCell maxSides values remaining →
      currentHeap[unused]? = some (.list (kinds (remaining.filter (fun other => decide (other ≠ kind))))) →
      value ∈ all → value ∉ values → ProjectEulerSolutions.PolygonalCycle.links last value = true →
      ∃ extra, ReturnsValue program "__formalsw_local_naive_extend"
        [.ref (currentHeap.length + 1), .ref unused, .ref familiesCell] (childHeap currentHeap values value)
        (number (visit value)) (childHeap currentHeap values value ++ extra) globals) :
    ∃ extra finalEnv, BlockContinues program env [.sequenceStepLoop "value" (.ref source) 0 innerBody []]
      heap finalEnv (heap ++ extra) globals ∧ Bindings finalEnv path remainingAddress familiesCell ∧
      finalEnv "best" = some (number (all.foldl (advance values last visit) best)) ∧
      HeapRangeFold.Frame ["value", "best"] env finalEnv := by
  let invariant := fun currentHeap currentEnv currentBest =>
    Nonempty (SearchState currentHeap path remainingAddress familiesCell maxSides values remaining) ∧
      Bindings currentEnv path remainingAddress familiesCell ∧ currentEnv "unused" = some (.ref unused) ∧
      currentHeap[unused]? = some (.list (kinds (remaining.filter (fun other => decide (other ≠ kind))))) ∧
      currentEnv "best" = some (number currentBest)
  have bindInvariant : ∀ currentHeap currentEnv currentBest value, invariant currentHeap currentEnv currentBest → value ∈ all →
      invariant currentHeap (setLocal currentEnv "value" (number value)) currentBest := by
    intro currentHeap currentEnv currentBest value good _
    obtain ⟨ready, currentBound, currentUnused, currentFound, currentBestFound⟩ := good
    refine ⟨ready, currentBound.local "value" (number value) (by decide), ?_, currentFound, ?_⟩
    · simpa [setLocal] using currentUnused
    · simpa [setLocal] using currentBestFound
  have cell : ∀ currentHeap currentEnv currentBest value, invariant currentHeap currentEnv currentBest → value ∈ all →
      currentEnv "value" = some (number value) →
      ∃ extra finalEnv, HeapLoop.Continues program currentEnv innerBody currentHeap finalEnv (currentHeap ++ extra) globals ∧
        invariant (currentHeap ++ extra) finalEnv (advance values last visit currentBest value) ∧
        HeapRangeFold.Frame ["value", "best"] currentEnv finalEnv := by
    intro currentHeap currentEnv currentBest value good member getValue
    obtain ⟨⟨current⟩, currentBound, currentUnused, currentFound, currentBestFound⟩ := good
    have unchanged : invariant currentHeap currentEnv currentBest :=
      ⟨⟨current⟩, currentBound, currentUnused, currentFound, currentBestFound⟩
    by_cases used : value ∈ values
    · refine ⟨[], currentEnv, ?_, ?_, HeapRangeFold.Frame.refl _ _⟩
      · simpa only [List.append_nil] using inner_used values currentHeap path current.pathFound value used currentEnv
          currentBound.getPath getValue globals
      · simpa only [advance, if_pos used, List.append_nil] using unchanged
    · cases linked : ProjectEulerSolutions.PolygonalCycle.links last value with
      | false =>
          refine ⟨[], currentEnv, ?_, ?_, HeapRangeFold.Frame.refl _ _⟩
          · simpa only [List.append_nil] using inner_unlinked values last atEnd currentHeap path current.pathFound value used linked
              currentEnv currentBound.getPath getValue globals
          · simpa only [advance, if_neg used, linked, Bool.false_eq_true, if_false, List.append_nil] using unchanged
      | true =>
          obtain ⟨extra, returned⟩ := child currentHeap value current currentFound member used linked
          let total : Mutable.Heap := [.list [number value], .list (numbers (values ++ [value]))] ++ extra
          have layout : childHeap currentHeap values value ++ extra = currentHeap ++ total := by
            simp only [childHeap, total, List.append_assoc]
          rw [layout] at returned
          let finalEnv := setLocal currentEnv "best" (number (max currentBest (visit value)))
          have finalGood : invariant (currentHeap ++ total) finalEnv (max currentBest (visit value)) := by
            refine ⟨⟨current.append total⟩, currentBound.local "best" _ (by decide), ?_, ?_, rfl⟩
            · simpa [finalEnv, setLocal] using currentUnused
            · exact HeapCollection.prefix_found _ _ _ _ currentFound
          refine ⟨total, finalEnv, ?_, ?_, HeapRangeFold.Frame.updated _ currentEnv "best" _ (by decide)⟩
          · exact inner_updated values last atEnd currentHeap path unused familiesCell current.pathFound value currentBest
              (visit value) used linked currentEnv currentBound.getPath getValue currentUnused currentBestFound currentBound.getCell returned
          · simpa only [advance, if_neg used, linked, if_true] using finalGood
  obtain ⟨extra, finalEnv, executed, good, frame⟩ := HeapLoop.fold program "value" innerBody rfl ["value", "best"] (by decide)
    number (advance values last visit) invariant source all bindInvariant cell all 0 rfl heap env best
    ⟨⟨state⟩, bound, getUnused, unusedFound, getBest⟩ found
  exact ⟨extra, finalEnv, executed, good.2.1, good.2.2.2.2, frame⟩

def advanceKind (values : List Int) (last : Int) (visit : Int → Int → Int) (best : Int) (kind : Int) : Int :=
  (PolygonalFamilies.family kind).foldl (advance values last (visit kind)) best

/-- The source's type loop composes unused-type construction with the complete candidate fold. -/
theorem type_loop (state : SearchState heap path remainingAddress familiesCell maxSides values remaining)
    (bound : Bindings env path remainingAddress familiesCell) (last : Int) (atEnd : values.getLast? = some last)
    (best : Int) (getBest : env "best" = some (number best)) (visit : Int → Int → Int)
    (child : ∀ currentHeap kind unused value, SearchState currentHeap path remainingAddress familiesCell maxSides values remaining →
      kind ∈ remaining →
      currentHeap[unused]? = some (.list (kinds (remaining.filter (fun other => decide (other ≠ kind))))) →
      value ∈ PolygonalFamilies.family kind → value ∉ values →
      ProjectEulerSolutions.PolygonalCycle.links last value = true →
      ∃ extra, ReturnsValue program "__formalsw_local_naive_extend"
        [.ref (currentHeap.length + 1), .ref unused, .ref familiesCell] (childHeap currentHeap values value)
        (number (visit kind value)) (childHeap currentHeap values value ++ extra) globals) :
    ∃ extra finalEnv, BlockContinues program env [.forIn (.name "kind") (.name "remaining") outerBody []]
      heap finalEnv (heap ++ extra) globals ∧ Bindings finalEnv path remainingAddress familiesCell ∧
      finalEnv "best" = some (number (remaining.foldl (advanceKind values last visit) best)) ∧
      HeapRangeFold.Frame ["kind", "unused", "value", "best"] env finalEnv := by
  let invariant := fun currentHeap currentEnv currentBest =>
    Nonempty (SearchState currentHeap path remainingAddress familiesCell maxSides values remaining) ∧
      Bindings currentEnv path remainingAddress familiesCell ∧ currentEnv "best" = some (number currentBest)
  have bindInvariant : ∀ currentHeap currentEnv currentBest kind, invariant currentHeap currentEnv currentBest → kind ∈ remaining →
      invariant currentHeap (setLocal currentEnv "kind" (number kind)) currentBest := by
    intro currentHeap currentEnv currentBest kind good _
    obtain ⟨ready, currentBound, currentBestFound⟩ := good
    exact ⟨ready, currentBound.local "kind" _ (by decide), by simpa [setLocal] using currentBestFound⟩
  have cell : ∀ currentHeap currentEnv currentBest kind, invariant currentHeap currentEnv currentBest → kind ∈ remaining →
      currentEnv "kind" = some (number kind) →
      ∃ afterEnv finalHeap, BlockContinues program currentEnv outerBody currentHeap afterEnv finalHeap globals ∧
        invariant finalHeap afterEnv (advanceKind values last visit currentBest kind) ∧
        (∃ extra, finalHeap = currentHeap ++ extra) ∧
        HeapRangeFold.Frame ["kind", "unused", "value", "best"] currentEnv afterEnv := by
    intro currentHeap currentEnv currentBest kind good member getKind
    obtain ⟨⟨current⟩, currentBound, currentBestFound⟩ := good
    let filtered := remaining.filter (fun other => decide (other ≠ kind))
    let middle := currentHeap ++ [.list (kinds filtered)]
    let readyEnv := setLocal currentEnv "unused" (.ref currentHeap.length)
    let ready := current.append [.list (kinds filtered)]
    have readyBound : Bindings readyEnv path remainingAddress familiesCell := currentBound.local "unused" _ (by decide)
    have readyBest : readyEnv "best" = some (number currentBest) := by simpa [readyEnv, setLocal] using currentBestFound
    have readyKind : readyEnv "kind" = some (number kind) := by simpa [readyEnv, setLocal] using getKind
    have made := unused_evaluate remaining kind currentHeap remainingAddress current.remainingFound currentEnv
      currentBound.getRemaining getKind globals
    have looked := family_evaluate ready.world kind (current.validKinds kind member) readyEnv readyBound.getCell readyKind globals
    obtain ⟨extra, finalEnv, scanned, finalBound, finalBest, frame⟩ := candidate_loop ready readyBound last atEnd kind currentHeap.length
      (by simp [filtered]) rfl currentBest readyBest
      (PolygonalFamilies.family kind) (ready.world.target kind)
      (ready.world.familyFound kind (current.validKinds kind member)) (visit kind)
      (fun nextHeap value ready found inFamily fresh linked => child nextHeap kind currentHeap.length value ready member found inFamily fresh linked)
    have header : BlockContinues program readyEnv [.forIn (.name "value") familyExpression innerBody []]
        middle finalEnv (middle ++ extra) globals := by
      apply BlockContinues.for_sequence (items := numbers (PolygonalFamilies.family kind))
        (by intro expressions impossible; cases impossible) looked
        (by simp [Mutable.sequence, ready.world.familyFound kind (current.validKinds kind member)])
      exact scanned
    have emitted := (BlockContinues.assign (name := "unused") made).append header
    let total : Mutable.Heap := .list (kinds filtered) :: extra
    have layout : middle ++ extra = currentHeap ++ total := by simp [middle, total, List.append_assoc]
    rw [layout] at emitted
    have widened : HeapRangeFold.Frame ["kind", "unused", "value", "best"] readyEnv finalEnv := by
      intro name outside
      exact frame name (fun member => outside (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))
    refine ⟨finalEnv, currentHeap ++ total, emitted, ⟨⟨current.append total⟩, finalBound, finalBest⟩,
      ⟨total, rfl⟩, ?_⟩
    exact (HeapRangeFold.Frame.updated _ currentEnv "unused" (.ref currentHeap.length) (by decide)).trans widened
  obtain ⟨finalEnv, finalHeap, executed, good, ⟨extra, layout⟩, frame⟩ := HeapSequenceFold.for_list program "kind" outerBody rfl
    ["kind", "unused", "value", "best"] (by decide) (fun kind : Int => number kind)
    (advanceKind values last visit) invariant remainingAddress remaining bindInvariant cell heap env best
    ⟨⟨state⟩, bound, getBest⟩ (.name "remaining") (by intro expressions impossible; cases impossible)
    (Evaluates.lookup bound.getRemaining) state.remainingFound
  rw [layout] at executed
  exact ⟨extra, finalEnv, executed, good.2.1, good.2.2, frame⟩
end data.«project-euler-statements».data.py.project_euler_statements.p61.extend
