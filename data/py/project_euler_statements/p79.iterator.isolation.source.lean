import data.«project-euler-statements».data.py.project_euler_statements.«p79.iterator.source»
import lang.py.FormalSW.IteratorExecutionIsolation

/-! A logical next-method execution supplies validation and preservation of the private checked list. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation
set_option Elab.async false

/-- No physical method execution or post-method private-list invariant is assumed. -/
theorem iterator_accepted_from_logical (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule) (anchors used finalUsed : Nat)
    (logical physical yielded : Mutable.Heap) (rename : Nat → Nat)
    (iterator : Mutable.Value) (operation : Operation) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (s : String) (length : s.length = 3) (digits : Strings.isDigit s = true)
    (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (inside : iterator.edge.Within logical.length)
    (isObject : IteratorCalls.isInstance logical iterator = true)
    (bound : ProtocolCalls.nextMethod context iterator logical = some (.ok (some operation), logical))
    (executed : IteratorCalls.Reaches context logical.length choices []
      (.running ⟨⟨.operation operation [], [], logical⟩, used⟩ [])
      (.completed (.ok ⟨.ok (text s), [], yielded, logical.length⟩) finalUsed []))
    (noGrowth : yielded.length = logical.length)
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (stack : List HeapCalls.Frame) (resumes : List IteratorCalls.Resume) :
    ∃ (other : Mutable.Heap) (nextMap : Nat → Nat),
      (∀ index < logical.length, nextMap index = rename index) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop
          (sequenceSource (relocateValue rename iterator)) 0 :: following) env, stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block (validationLoop
          (sequenceSource (relocateValue rename iterator)) 0 :: following)
          (setLocal env "attempt" (text s)), stack,
          other.set address (.list ((checked ++ [s]).map text))⟩, finalUsed⟩ resumes) ∧
      PrivateLayout yielded (other.set address (.list ((checked ++ [s]).map text))) nextMap
        address (.list ((checked ++ [s]).map text)) := by
  obtain ⟨other, nextMap, extended, kept, called⟩ := IteratorCalls.Relocation.advance_completion_isolated
    context choices logical physical rename logical.length anchors used finalUsed iterator operation (.ok (text s))
    yielded [] source layout.layout inside (by simp [HeapCalls.Relocation.GlobalsWithin]) isObject bound executed noGrowth
  have retainedList := kept address (.list (checked.map text)) layout
  have completion : IteratorCalls.Reaches context anchors choices []
      (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following) env,
        stack, physical⟩, used⟩ resumes)
      (.completed (.ok ⟨.ok (text s), [], other, anchors⟩) finalUsed
        (.advance (validationIteratorLoop env following stack) (relocateValue rename iterator) :: resumes)) := by
    simpa only [HeapCalls.Relocation.relocateGlobals, List.map_nil, Except.map, text, relocateValue] using
      called (validationIteratorLoop env following stack) resumes
  have body := accepted_attempt_at other address checked (setLocal env "attempt" (text s)) s
    retainedList.saved (by simpa [setLocal] using getChecked) (by simp [setLocal]) length digits
  refine ⟨other, nextMap, extended.agrees, ?_, retainedList.update_private _ (by simp) (by simp)⟩
  apply (IteratorCalls.advanced completion).trans
  have resumed := IteratorCalls.Reaches.of_heap (choices := choices) (used := finalUsed)
    ((body.extend extension) (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
      anchors stack) resumes
  simpa only [IteratorCalls.loopCode, validationIteratorLoop, Calls.loopContinuation,
    show Calls.loopControl validationBody = false from rfl, Bool.false_eq_true, ↓reduceIte,
    List.append_assoc, List.singleton_append] using resumed

end data.«project-euler-statements».data.py.project_euler_statements.p79
