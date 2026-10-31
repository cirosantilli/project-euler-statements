import data.«project-euler-statements».data.py.project_euler_statements.«p79.py.lean.d».Terminal
import data.«project-euler-statements».data.py.project_euler_statements.«p79.py.lean.d».Allocation
import data.«project-euler-statements».data.py.project_euler_statements.«p79.py.lean.d».Acquisition
import lang.py.FormalSW.IteratorTerminal

namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

/-- Execute initialization, acquisition and a valid prefix before a possibly allocating final call. -/
theorem naive_allocating_prefix_entry
    (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired middle : Mutable.Heap)
    (acquiredUsed nextUsed : Nat) (closed : Closed base)
    (acquisition : AllocatingAcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String)
    (trace : AllocatingYieldPrefix context choices iterator text acquired acquiredUsed attempts middle nextUsed)
    (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true) :
    ∃ physical env rename, ExecutionLayout middle physical rename ∧
      (∀ index < base.length, rename index = index) ∧
      IteratorCalls.Reaches context base.length choices []
        (.running ⟨⟨.operation (.call "naive") [receiver], [], base⟩, 0⟩ [])
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: [.return checkedExpression]) env,
          [], physical⟩, nextUsed⟩ []) := by
  obtain ⟨acquiredClosed, acquisitionGrows, iteratorInside⟩ := acquisition.acquireRun.effects source closed
  obtain ⟨initialized, entryMap, layout, entryFixed, entered⟩ := naive_allocating_entry context extension source choices receiver iterator
    base acquired 0 acquiredUsed base.length closed acquisition [] []
  obtain ⟨physical, env, rename, agrees, finalPrivate, _, accepted⟩ := validated_allocating_prefix context extension source choices
    iterator acquired middle acquiredUsed nextUsed attempts trace valid initialized entryMap base.length []
      (iteratorEntryEnv base receiver) layout (by simp [iteratorEntryEnv, setLocal]) [.return checkedExpression] base.length [] []
  have sameIterator := relocateValue_congr rename entryMap acquired.length iterator agrees iteratorInside
  refine ⟨physical, env, rename, finalPrivate.layout, ?_, ?_⟩
  · intro index bounded
    exact (agrees index (by omega)).trans (entryFixed index bounded)
  · simpa only [sameIterator] using entered.trans accepted

/-- The final failing method may allocate; its caller-visible graph and exact error survive. -/
theorem naive_allocating_terminal_failure
    (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired middle : Mutable.Heap)
    (acquiredUsed nextUsed : Nat) (closed : Closed base)
    (acquisition : AllocatingAcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String)
    (trace : AllocatingYieldPrefix context choices iterator text acquired acquiredUsed attempts middle nextUsed)
    (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true)
    (failed : Mutable.Heap) (finalUsed : Nat) (error : ExceptionObject)
    (ran : NextRun context choices iterator middle nextUsed (.error error) failed finalUsed)
    (notExhausted : error.typeName ≠ "StopIteration") :
    ∃ after rename, ExecutionLayout failed after rename ∧
      (∀ index < base.length, rename index = index) ∧
      ((IteratorCalls.call context "naive" [receiver] base).run choices).Finishes
        ⟨.error error, [], after, base.length⟩ := by
  obtain ⟨physical, env, entryMap, layout, entryFixed, entered⟩ := naive_allocating_prefix_entry context extension source choices receiver iterator
    base acquired middle acquiredUsed nextUsed closed acquisition attempts trace valid
  obtain ⟨acquiredClosed, acquisitionGrows, _⟩ := acquisition.acquireRun.effects source closed
  have prefixGrows := (trace.yieldPrefix.effects source acquiredClosed).2
  obtain ⟨after, rename, extended, failed⟩ := ran.failure_relocates notExhausted source physical entryMap layout base.length
  refine ⟨after, rename, extended.layout, fun index bounded => (extended.agrees index (by omega)).trans (entryFixed index bounded), ?_⟩
  exact (entered.trans (by simpa only [loopCode, validationIteratorLoop, relocateValue_id] using (failed (validationIteratorLoop env [.return checkedExpression] ([])) []))).finishes (.done rfl)

/-- Reject a malformed scalar after the final iterator method's allocations and mutations. -/
theorem naive_allocating_terminal_rejection
    (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired middle : Mutable.Heap)
    (acquiredUsed nextUsed : Nat) (closed : Closed base)
    (acquisition : AllocatingAcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String)
    (trace : AllocatingYieldPrefix context choices iterator text acquired acquiredUsed attempts middle nextUsed)
    (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true)
    (yielded : Mutable.Heap) (finalUsed : Nat) (s : String)
    (ran : NextRun context choices iterator middle nextUsed (.ok (text s)) yielded finalUsed)
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false) :
    ∃ after rename, ExecutionLayout yielded after rename ∧
      (∀ index < base.length, rename index = index) ∧
      ((IteratorCalls.call context "naive" [receiver] base).run choices).Finishes
        ⟨.error (invalidException s), [], after, base.length⟩ := by
  obtain ⟨physical, env, entryMap, layout, entryFixed, entered⟩ := naive_allocating_prefix_entry context extension source choices receiver iterator
    base acquired middle acquiredUsed nextUsed closed acquisition attempts trace valid
  obtain ⟨acquiredClosed, acquisitionGrows, _⟩ := acquisition.acquireRun.effects source closed
  have prefixGrows := (trace.yieldPrefix.effects source acquiredClosed).2
  obtain ⟨after, rename, extended, rejected⟩ := terminal_rejection_relocates context extension source choices iterator
    middle yielded physical nextUsed finalUsed base.length s invalid ran entryMap layout env [.return checkedExpression] ([]) []
  refine ⟨after, rename, extended.layout, fun index bounded => (extended.agrees index (by omega)).trans (entryFixed index bounded), ?_⟩
  exact (entered.trans (by simpa only [relocateValue_id] using rejected)).finishes (.done rfl)

end data.«project-euler-statements».data.py.project_euler_statements.p79
