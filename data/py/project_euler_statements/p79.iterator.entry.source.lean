import data.«project-euler-statements».data.py.project_euler_statements.«p79.iterator.prefix.source»
import data.«project-euler-statements».data.py.project_euler_statements.«p79.iterator.traversal.source»
import data.«project-euler-statements».data.py.project_euler_statements.«p79.naive.source»
import lang.py.FormalSW.IteratorAcquisitionIsolation

/-! The reference call allocates its checked list, acquires the iterator and retains acquisition effects. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

def iteratorEntryEnv (base : Mutable.Heap) (receiver : Mutable.Value) : HeapCalls.Env :=
  setLocal (functionEnv naiveArgs naiveBody [receiver] []) "checked" (.ref base.length)

theorem naive_iterator_initialize (base : Mutable.Heap) (receiver : Mutable.Value) (anchors : Nat)
    (stack : List HeapCalls.Frame) :
    HeapCalls.Reaches program anchors ⟨.operation (.call "naive") [receiver], stack, base⟩
      ⟨.block [.forIn (.name "attempt") (.name "attempts") validationBody [], .return checkedExpression]
        (iteratorEntryEnv base receiver), stack, base ++ [.list []]⟩ := by
  apply HeapCalls.Reaches.next (following :=
    ⟨.block naiveCode (functionEnv naiveArgs naiveBody [receiver] []), stack, base⟩) rfl
  have allocated : BlockContinues program (functionEnv naiveArgs naiveBody [receiver] [])
      [.annAssign (.name "checked") (.subscript (.name "list") (.name "str")) (some (.list []))]
      base (iteratorEntryEnv base receiver) (base ++ [.list []]) :=
    BlockContinues.annAssign (Evaluates.list .nil)
  simpa only [naive_source] using allocated
    [.forIn (.name "attempt") (.name "attempts") validationBody [], .return checkedExpression] anchors stack

theorem naive_iterator_entry (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired : Mutable.Heap) (used finalUsed anchors : Nat)
    (closed : Closed base) (ran : AcquireRun context choices receiver base used iterator acquired finalUsed)
    (noGrowth : acquired.length = base.length) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after, PrivateLayout acquired after id base.length (.list []) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.operation (.call "naive") [receiver], stack, base⟩, used⟩ resumes)
        (.running ⟨⟨.block [validationLoop (sequenceSource iterator) 0, .return checkedExpression]
          (iteratorEntryEnv base receiver), stack, after⟩, finalUsed⟩ resumes) := by
  have layout := (ExecutionLayout.refl base closed).new_private_cell (.list []) (by simp)
  obtain ⟨after, _, kept, entered⟩ := ran.for_name_isolated source (base ++ [.list []]) id layout.layout noGrowth anchors
  refine ⟨after, kept base.length _ layout, ?_⟩
  apply (IteratorCalls.Reaches.of_heap ((naive_iterator_initialize base receiver anchors stack).extend extension) resumes).trans
  simpa only [relocateValue_id, loopCode, validationIteratorLoop] using entered
    (validationIteratorLoop (iteratorEntryEnv base receiver) [.return checkedExpression] stack) resumes "attempts"
    (by simpa only [relocateValue_id] using
      (show iteratorEntryEnv base receiver "attempts" = some receiver from rfl))

theorem naive_iterator_rejection (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired middle yielded : Mutable.Heap)
    (acquiredUsed nextUsed finalUsed : Nat) (closed : Closed base)
    (acquisition : AcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String) (s : String)
    (trace : YieldPrefix context choices iterator text acquired acquiredUsed attempts middle nextUsed)
    (ran : NextRun context choices iterator middle nextUsed (.ok (text s)) yielded finalUsed)
    (noGrowth : yielded.length = base.length)
    (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true)
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false) :
    ∃ after, PrivateLayout yielded after id base.length (.list (attempts.map text)) ∧
      ((IteratorCalls.call context "naive" [receiver] base).run choices).Finishes
        ⟨.error (invalidException s), [], after, base.length⟩ := by
  obtain ⟨acquiredClosed, acquisitionGrows, _⟩ := acquisition.effects source closed
  obtain ⟨middleClosed, prefixGrows⟩ := trace.effects source acquiredClosed
  have lastGrows := (ran.effects source middleClosed).2
  obtain ⟨initialized, layout, entered⟩ := naive_iterator_entry context extension source choices receiver iterator
    base acquired 0 acquiredUsed base.length closed acquisition (by omega) [] []
  obtain ⟨after, finalPrivate, failed⟩ := reject_after_iterator_prefix context extension source choices iterator
    acquired middle yielded acquiredUsed nextUsed finalUsed attempts s trace ran (by omega) valid invalid
      initialized id base.length [] (iteratorEntryEnv base receiver) layout
      (by simp [iteratorEntryEnv, setLocal]) [.return checkedExpression] base.length [] []
  refine ⟨after, by simpa only [List.nil_append] using finalPrivate, ?_⟩
  exact (entered.trans (by simpa only [relocateValue_id] using failed)).finishes (.done rfl)

theorem naive_iterator_failure (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired yielded : Mutable.Heap)
    (acquiredUsed finalUsed : Nat) (closed : Closed base)
    (acquisition : AcquireRun context choices receiver base 0 iterator acquired acquiredUsed)
    (attempts : List String) (error : ExceptionObject)
    (trace : Traversal context choices iterator text acquired acquiredUsed attempts (.error error) yielded finalUsed)
    (noGrowth : yielded.length = base.length)
    (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true) :
    ∃ after, PrivateLayout yielded after id base.length (.list (attempts.map text)) ∧
      ((IteratorCalls.call context "naive" [receiver] base).run choices).Finishes
        ⟨.error error, [], after, base.length⟩ := by
  obtain ⟨acquiredClosed, acquisitionGrows, _⟩ := acquisition.effects source closed
  have traversalGrows := (trace.effects source acquiredClosed).2
  obtain ⟨initialized, layout, entered⟩ := naive_iterator_entry context extension source choices receiver iterator
    base acquired 0 acquiredUsed base.length closed acquisition (by omega) [] []
  obtain ⟨after, _, finalPrivate, _, failed⟩ := validated_iterator_traversal context extension source choices iterator
    acquired yielded acquiredUsed finalUsed attempts (.error error) trace (by omega) valid
      initialized id base.length [] (iteratorEntryEnv base receiver) layout
      (by simp [iteratorEntryEnv, setLocal]) [.return checkedExpression] base.length [] []
  refine ⟨after, by simpa only [List.nil_append] using finalPrivate, ?_⟩
  exact (entered.trans (by simpa only [ExitResult, relocateValue_id] using failed)).finishes (.done rfl)

end data.«project-euler-statements».data.py.project_euler_statements.p79
