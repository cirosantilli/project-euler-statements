import data.«project-euler-statements».data.py.project_euler_statements.«p79.py.lean.d».Terminal
import lang.py.FormalSW.IteratorAcquisitionFailure
import data.«project-euler-statements».data.py.project_euler_statements.«p79.py.lean.d».Execution

namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

/-- Exhausted input continues through the reference's actual graph construction and return expression. -/
theorem naive_iterator_result (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired yielded : Mutable.Heap)
    (acquiredUsed finalUsed : Nat) (closed : Closed base)
    (acquisition : AcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String)
    (trace : Traversal context choices iterator text acquired acquiredUsed attempts (.ok ()) yielded finalUsed)
    (noGrowth : yielded.length = base.length)
    (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true) :
    ∃ after, RuntimeLayout yielded after id ∧
      ((IteratorCalls.call context "naive" [receiver] base).run choices).Finishes
        ⟨checkedOutcome attempts, [], after, base.length⟩ := by
  obtain ⟨acquiredClosed, acquisitionGrows, _⟩ := acquisition.effects source closed
  have traversalGrows := (trace.effects source acquiredClosed).2
  obtain ⟨initialized, layout, entered⟩ := naive_iterator_entry context extension source choices receiver iterator
    base acquired 0 acquiredUsed base.length closed acquisition (by omega) [] []
  obtain ⟨middle, finalEnv, finalPrivate, getChecked, exhausted⟩ := validated_iterator_traversal
    context extension source choices iterator acquired yielded acquiredUsed finalUsed attempts (.ok ()) trace
      (by omega) valid initialized id base.length [] (iteratorEntryEnv base receiver) layout
      (by simp [iteratorEntryEnv, setLocal]) [.return checkedExpression] base.length [] []
  obtain ⟨after, returned, retained⟩ := checked_return_result middle base.length attempts
    (by simpa only [List.nil_append] using finalPrivate.saved) finalEnv getChecked
  refine ⟨after, ?_, ?_⟩
  · obtain ⟨extra, rfl⟩ := retained
    exact finalPrivate.layout.runtime.append_private extra
  · have finished := HeapCalls.finishes_extend (SourceResult.finishes _ _ _ _ returned base.length) extension
    have continued := IteratorCalls.finishes_of_set (SetCalls.finishes_of_heap finished choices finalUsed) (by
      intro completion same
      cases same
      unfold checkedOutcome
      split <;> simp [cycleException])
    apply (entered.trans (by simpa only [ExitResult, relocateValue_id, validationIteratorLoop,
      List.nil_append] using exhausted)).finishes continued

end data.«project-euler-statements».data.py.project_euler_statements.p79

namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

/-- Failed iterator acquisition exits the actual reference call before any input is validated. -/
theorem naive_acquisition_failure (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver : Mutable.Value) (base failed : Mutable.Heap) (finalUsed : Nat) (error : ExceptionObject)
    (closed : Closed base) (failure : AcquireFailure context choices receiver base 0 error failed finalUsed) :
    ∃ after rename, ExecutionLayout failed after rename ∧
      (∀ index < base.length, rename index = index) ∧
      ((IteratorCalls.call context "naive" [receiver] base).run choices).Finishes
        ⟨.error error, [], after, base.length⟩ := by
  have layout := (ExecutionLayout.refl base closed).append_private_nonempty (.list []) (by simp)
  obtain ⟨after, rename, extended, rejected⟩ := failure.for_name_relocates source (base ++ [.list []]) id
    layout base.length
  have actual := rejected (validationIteratorLoop (iteratorEntryEnv base receiver) [.return checkedExpression] [])
    [] "attempts" (by simpa only [relocateValue_id] using
      (show iteratorEntryEnv base receiver "attempts" = some receiver from rfl))
  refine ⟨after, rename, extended.layout, extended.agrees, ?_⟩
  have entered := IteratorCalls.Reaches.of_heap (choices := choices) (used := 0)
    ((naive_iterator_initialize base receiver base.length []).extend extension) []
  exact (entered.trans (by simpa only [validationIteratorLoop, Calls.generatorException,
    List.any_nil, Bool.false_and, Bool.false_eq_true, ↓reduceIte] using actual)).finishes (.done rfl)

end data.«project-euler-statements».data.py.project_euler_statements.p79
