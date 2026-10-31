import data.«project-euler-statements».data.py.project_euler_statements.«p79.py.lean.d».Execution
import lang.py.FormalSW.IteratorAllocatingAcquisition

namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

theorem naive_allocating_entry (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (receiver iterator : Mutable.Value) (base acquired : Mutable.Heap) (used finalUsed anchors : Nat)
    (closed : Closed base) (ran : AllocatingAcquireRun context choices receiver base used iterator acquired finalUsed)
    (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after rename, PrivateLayout acquired after rename base.length (.list []) ∧
      (∀ index < base.length, rename index = index) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.operation (.call "naive") [receiver], stack, base⟩, used⟩ resumes)
        (.running ⟨⟨.block [validationLoop (sequenceSource (relocateValue rename iterator)) 0, .return checkedExpression]
          (iteratorEntryEnv base receiver), stack, after⟩, finalUsed⟩ resumes) := by
  have layout := (ExecutionLayout.refl base closed).new_private_cell (.list []) (by simp)
  obtain ⟨after, rename, extended, kept, entered⟩ := ran.for_name_isolated source (base ++ [.list []]) id layout.layout anchors
  refine ⟨after, rename, kept base.length _ (by simp) layout, extended.agrees, ?_⟩
  apply (IteratorCalls.Reaches.of_heap ((naive_iterator_initialize base receiver anchors stack).extend extension) resumes).trans
  simpa only [loopCode, validationIteratorLoop] using entered
    (validationIteratorLoop (iteratorEntryEnv base receiver) [.return checkedExpression] stack) resumes "attempts"
    (by simpa only [relocateValue_id] using
      (show iteratorEntryEnv base receiver "attempts" = some receiver from rfl))

end data.«project-euler-statements».data.py.project_euler_statements.p79
