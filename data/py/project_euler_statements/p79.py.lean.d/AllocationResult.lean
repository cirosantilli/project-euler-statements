import data.«project-euler-statements».data.py.project_euler_statements.«p79.py.lean.d».Allocation

namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

theorem naive_allocating_result (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired middle yielded : Mutable.Heap)
    (acquiredUsed nextUsed finalUsed : Nat) (closed : Closed base)
    (acquisition : AcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String)
    (trace : AllocatingYieldPrefix context choices iterator text acquired acquiredUsed attempts middle nextUsed)
    (args : List Constant)
    (last : AllocatingNextRun context choices iterator middle nextUsed (.error ⟨"StopIteration", args⟩) yielded finalUsed)
    (acquisitionSize : acquired.length = base.length)
    (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true) :
    ∃ after finalMap, RuntimeLayout yielded after finalMap ∧
      (∀ index < base.length, finalMap index = index) ∧
      ((IteratorCalls.call context "naive" [receiver] base).run choices).Finishes
        ⟨checkedOutcome attempts, [], after, base.length⟩ := by
  obtain ⟨acquiredClosed, _, iteratorInside⟩ := acquisition.effects source closed
  have prefixGrows := (trace.yieldPrefix.effects source acquiredClosed).2
  obtain ⟨initialized, layout, entered⟩ := naive_iterator_entry context extension source choices receiver iterator
    base acquired 0 acquiredUsed base.length closed acquisition acquisitionSize [] []
  obtain ⟨prefixHeap, finalEnv, prefixMap, agrees, prefixPrivate, getChecked, consumed⟩ := validated_allocating_prefix
    context extension source choices iterator acquired middle acquiredUsed nextUsed attempts trace valid initialized id
      base.length [] (iteratorEntryEnv base receiver) layout (by simp [iteratorEntryEnv, setLocal])
      [.return checkedExpression] base.length [] []
  obtain ⟨middleHeap, finalMap, extended, kept, exited⟩ := last.exit_isolated source prefixHeap prefixMap prefixPrivate.layout base.length
  have finalPrivate := kept base.length _ (by simp) prefixPrivate
  have sameIterator : relocateValue prefixMap iterator = iterator := by
    simpa only [relocateValue_id] using relocateValue_congr prefixMap id acquired.length iterator agrees iteratorInside
  have exhausted := consumed.trans (by simpa only [ExitResult, exitOutcome, if_pos rfl, sameIterator,
    relocateValue_id, validationIteratorLoop, loopCode, List.nil_append] using
      (exited (validationIteratorLoop finalEnv [.return checkedExpression] []) []))
  obtain ⟨after, returned, retained⟩ := checked_return_result middleHeap base.length attempts
    (by simpa only [List.nil_append] using finalPrivate.saved) finalEnv getChecked
  refine ⟨after, finalMap, ?_, ?_, ?_⟩
  · obtain ⟨extra, rfl⟩ := retained
    exact finalPrivate.layout.runtime.append_private extra
  · intro index bounded
    exact (extended.agrees index (by omega)).trans (agrees index (by omega))
  · have finished := HeapCalls.finishes_extend (SourceResult.finishes _ _ _ _ returned base.length) extension
    have continued := IteratorCalls.finishes_of_set (SetCalls.finishes_of_heap finished choices finalUsed) (by
      intro completion same
      cases same
      unfold checkedOutcome
      split <;> simp [cycleException])
    apply (entered.trans (by simpa only [ExitResult, relocateValue_id, validationIteratorLoop,
      List.nil_append] using exhausted)).finishes continued


end data.«project-euler-statements».data.py.project_euler_statements.p79
