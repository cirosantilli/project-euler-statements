import data.«project-euler-statements».data.py.project_euler_statements.«p79.py.lean.d».Execution
import lang.py.FormalSW.IteratorAllocatingRun

namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

theorem iterator_accepted_from_allocating (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule) (anchors used finalUsed : Nat)
    (logical physical yielded : Mutable.Heap) (rename : Nat → Nat)
    (iterator : Mutable.Value) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (s : String) (length : s.length = 3) (digits : Strings.isDigit s = true)
    (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (ran : IteratorCalls.AllocatingNextRun context choices iterator logical used (.ok (text s)) yielded finalUsed)
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
  obtain ⟨other, nextMap, extended, kept, called⟩ := ran.advance_isolated source physical rename layout.layout anchors
  have retainedList := kept address (.list (checked.map text)) (by simp) layout
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


theorem validated_allocating_prefix (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (logical finalLogical : Mutable.Heap) (used finalUsed : Nat) (attempts : List String)
    (trace : AllocatingYieldPrefix context choices iterator text logical used attempts finalLogical finalUsed)
    (valid : ∀ s ∈ attempts, s.length = 3 ∧ Strings.isDigit s = true)
    (physical : Mutable.Heap) (rename : Nat → Nat) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after finalEnv finalMap,
      (∀ index < logical.length, finalMap index = rename index) ∧
      PrivateLayout finalLogical after finalMap address (.list ((checked ++ attempts).map text)) ∧
      finalEnv "checked" = some (.ref address) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          env, stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          finalEnv, stack, after⟩, finalUsed⟩ resumes) := by
  induction trace generalizing physical rename checked env with
  | nil => exact ⟨physical, env, rename, fun _ _ => rfl,
      by simpa only [List.append_nil] using layout, getChecked, .refl⟩
  | @cons before middle after used nextUsed finalUsed s rest ran later ih =>
    have firstGrows := (ran.nextRun.effects source layout.layout.closed).2
    have accepted := valid s (by simp)
    obtain ⟨yieldedPhysical, nextMap, agrees, iteration, nextPrivate⟩ :=
      iterator_accepted_from_allocating context extension source choices anchors used nextUsed before physical middle
        rename iterator address checked env s accepted.1 accepted.2 layout ran getChecked following stack resumes
    have sameIterator := relocateValue_congr nextMap rename before.length iterator agrees ran.nextRun.choose_spec.1
    obtain ⟨result, finalEnv, finalMap, finalAgrees, retained, finalChecked, continued⟩ :=
      ih (fun value member => valid value (List.mem_cons_of_mem _ member))
        _ nextMap (checked ++ [s]) (setLocal env "attempt" (text s)) nextPrivate
        (by simpa [setLocal] using getChecked)
    refine ⟨result, finalEnv, finalMap, ?_, ?_, finalChecked, iteration.trans ?_⟩
    · intro index bounded
      exact (finalAgrees index (Nat.lt_of_lt_of_le bounded firstGrows)).trans (agrees index bounded)
    · simpa only [List.append_assoc, List.singleton_append] using retained
    · simpa only [sameIterator] using continued

end data.«project-euler-statements».data.py.project_euler_statements.p79
