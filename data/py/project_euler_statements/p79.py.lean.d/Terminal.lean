import data.«project-euler-statements».data.py.project_euler_statements.«p79.py.lean.d».Execution
import lang.py.FormalSW.IteratorTerminal

namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

/-- Execute initialization, acquisition and a valid prefix before a possibly allocating final call. -/
theorem naive_iterator_prefix_entry
    (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired middle : Mutable.Heap)
    (acquiredUsed nextUsed : Nat) (closed : Closed base)
    (acquisition : AcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String)
    (trace : YieldPrefix context choices iterator text acquired acquiredUsed attempts middle nextUsed)
    (noGrowth : middle.length = base.length) (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true) :
    ∃ physical env, ExecutionLayout middle physical id ∧
      IteratorCalls.Reaches context base.length choices []
        (.running ⟨⟨.operation (.call "naive") [receiver], [], base⟩, 0⟩ [])
        (.running ⟨⟨.block (validationLoop (sequenceSource iterator) 0 :: [.return checkedExpression]) env,
          [], physical⟩, nextUsed⟩ []) := by
  obtain ⟨acquiredClosed, acquisitionGrows, _⟩ := acquisition.effects source closed
  have prefixGrows := (trace.effects source acquiredClosed).2
  obtain ⟨initialized, layout, entered⟩ := naive_iterator_entry context extension source choices receiver iterator
    base acquired 0 acquiredUsed base.length closed acquisition (by omega) [] []
  obtain ⟨physical, env, finalPrivate, _, accepted⟩ := validated_iterator_prefix context extension source choices
    iterator acquired middle acquiredUsed nextUsed attempts trace (by omega) valid initialized id base.length []
      (iteratorEntryEnv base receiver) layout (by simp [iteratorEntryEnv, setLocal]) [.return checkedExpression] base.length [] []
  exact ⟨physical, env, finalPrivate.layout, entered.trans (by simpa only [relocateValue_id] using accepted)⟩

/-- The final failing method may allocate; its caller-visible graph and exact error survive. -/
theorem naive_iterator_terminal_failure
    (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired middle : Mutable.Heap)
    (acquiredUsed nextUsed : Nat) (closed : Closed base)
    (acquisition : AcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String)
    (trace : YieldPrefix context choices iterator text acquired acquiredUsed attempts middle nextUsed)
    (noGrowth : middle.length = base.length) (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true)
    (failed : Mutable.Heap) (finalUsed : Nat) (error : ExceptionObject)
    (ran : NextRun context choices iterator middle nextUsed (.error error) failed finalUsed)
    (notExhausted : error.typeName ≠ "StopIteration") :
    ∃ after rename, ExecutionLayout failed after rename ∧
      (∀ index < base.length, rename index = index) ∧
      ((IteratorCalls.call context "naive" [receiver] base).run choices).Finishes
        ⟨.error error, [], after, base.length⟩ := by
  obtain ⟨physical, env, layout, entered⟩ := naive_iterator_prefix_entry context extension source choices receiver iterator
    base acquired middle acquiredUsed nextUsed closed acquisition attempts trace noGrowth valid
  obtain ⟨after, rename, extended, failed⟩ := ran.failure_relocates notExhausted source physical id layout base.length
  refine ⟨after, rename, extended.layout, fun index bounded => extended.agrees index (by omega), ?_⟩
  exact (entered.trans (by simpa only [loopCode, validationIteratorLoop, relocateValue_id] using (failed (validationIteratorLoop env [.return checkedExpression] ([])) []))).finishes (.done rfl)

theorem terminal_rejection_relocates (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (logical yielded physical : Mutable.Heap) (used finalUsed anchors : Nat)
    (s : String) (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false)
    (ran : NextRun context choices iterator logical used (.ok (text s)) yielded finalUsed)
    (rename : Nat → Nat)
    (layout : ExecutionLayout logical physical rename)
    (env : HeapCalls.Env) (following : List Stmt) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after nextMap, IteratorCalls.Relocation.ExtendedLayout logical.length physical.length rename yielded after nextMap ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          env, stack, physical⟩, used⟩ resumes)
        (.completed (.ok ⟨.error (invalidException s), [], after, anchors⟩) finalUsed resumes) := by
  obtain ⟨after, nextMap, extended, advanced⟩ := ran.scalar_relocates source physical rename layout anchors
  have rejected := rejected_attempt (setLocal env "attempt" (text s)) after s (by simp [setLocal]) invalid
    (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following) anchors stack
  have failed := completion_of_heap (choices := choices) (used := finalUsed) (finishes_extend rejected extension)
    (by intro completion same; cases same; simp [invalidException]) resumes
  refine ⟨after, nextMap, extended, (advanced (validationIteratorLoop env following stack) resumes).trans ?_⟩
  simpa only [loopCode, validationIteratorLoop, Calls.loopContinuation,
    show Calls.loopControl validationBody = false from rfl, Bool.false_eq_true, ↓reduceIte,
    List.append_assoc, List.singleton_append] using failed

/-- Reject a malformed scalar after the final iterator method's allocations and mutations. -/
theorem naive_iterator_terminal_rejection
    (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired middle : Mutable.Heap)
    (acquiredUsed nextUsed : Nat) (closed : Closed base)
    (acquisition : AcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String)
    (trace : YieldPrefix context choices iterator text acquired acquiredUsed attempts middle nextUsed)
    (noGrowth : middle.length = base.length) (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true)
    (yielded : Mutable.Heap) (finalUsed : Nat) (s : String)
    (ran : NextRun context choices iterator middle nextUsed (.ok (text s)) yielded finalUsed)
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false) :
    ∃ after rename, ExecutionLayout yielded after rename ∧
      (∀ index < base.length, rename index = index) ∧
      ((IteratorCalls.call context "naive" [receiver] base).run choices).Finishes
        ⟨.error (invalidException s), [], after, base.length⟩ := by
  obtain ⟨physical, env, layout, entered⟩ := naive_iterator_prefix_entry context extension source choices receiver iterator
    base acquired middle acquiredUsed nextUsed closed acquisition attempts trace noGrowth valid
  obtain ⟨after, rename, extended, rejected⟩ := terminal_rejection_relocates context extension source choices iterator
    middle yielded physical nextUsed finalUsed base.length s invalid ran id layout env [.return checkedExpression] ([]) []
  refine ⟨after, rename, extended.layout, fun index bounded => extended.agrees index (by omega), ?_⟩
  exact (entered.trans (by simpa only [relocateValue_id] using rejected)).finishes (.done rfl)

end data.«project-euler-statements».data.py.project_euler_statements.p79
