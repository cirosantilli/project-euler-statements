import data.«project-euler-statements».data.py.project_euler_statements.«p79.iterator.isolation.source»
import lang.py.FormalSW.IteratorPrefix

/-! Validation consumes a finite valid prefix and rejects the next invalid yield without reading further. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

theorem validated_iterator_prefix (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (logical finalLogical : Mutable.Heap) (used finalUsed : Nat) (attempts : List String)
    (trace : YieldPrefix context choices iterator text logical used attempts finalLogical finalUsed)
    (noGrowth : finalLogical.length = logical.length)
    (valid : ∀ s ∈ attempts, s.length = 3 ∧ Strings.isDigit s = true)
    (physical : Mutable.Heap) (rename : Nat → Nat) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after finalEnv,
      PrivateLayout finalLogical after rename address (.list ((checked ++ attempts).map text)) ∧
      finalEnv "checked" = some (.ref address) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          env, stack, physical⟩, used⟩ resumes)
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          finalEnv, stack, after⟩, finalUsed⟩ resumes) := by
  induction trace generalizing physical checked env with
  | nil => exact ⟨physical, env, by simpa only [List.append_nil] using layout, getChecked, .refl⟩
  | @cons before middle after used nextUsed finalUsed s rest ran later ih =>
      obtain ⟨middleClosed, firstGrows⟩ := ran.effects source layout.layout.closed
      have laterGrows := (later.effects source middleClosed).2
      have firstSize : middle.length = before.length := by omega
      have laterSize : after.length = middle.length := by omega
      obtain ⟨operation, inside, isObject, bound, executed⟩ := ran
      have accepted := valid s (by simp)
      obtain ⟨yieldedPhysical, nextMap, agrees, iteration, nextPrivate⟩ :=
        iterator_accepted_from_logical context extension source choices anchors used nextUsed before physical middle
          rename iterator operation address checked env s accepted.1 accepted.2 layout inside isObject bound
          executed firstSize getChecked following stack resumes
      have fixedMap : PrivateLayout middle
          (yieldedPhysical.set address (.list ((checked ++ [s]).map text))) rename
          address (.list ((checked ++ [s]).map text)) :=
        nextPrivate.congr (fun index bounded => (agrees index (by omega)).symm)
      obtain ⟨result, finalEnv, retained, finalChecked, continued⟩ := ih laterSize
        (fun value member => valid value (List.mem_cons_of_mem _ member))
        _ (checked ++ [s]) (setLocal env "attempt" (text s)) fixedMap
        (by simpa [setLocal] using getChecked)
      refine ⟨result, finalEnv, ?_, finalChecked, iteration.trans continued⟩
      simpa only [List.append_assoc, List.singleton_append] using retained

theorem iterator_rejected_from_logical (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (logical yielded physical : Mutable.Heap) (used finalUsed anchors : Nat)
    (s : String) (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false)
    (ran : NextRun context choices iterator logical used (.ok (text s)) yielded finalUsed)
    (noGrowth : yielded.length = logical.length) (rename : Nat → Nat)
    (address : Nat) (checked : List String)
    (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (env : HeapCalls.Env) (following : List Stmt) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after, PrivateLayout yielded after rename address (.list (checked.map text)) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          env, stack, physical⟩, used⟩ resumes)
        (.completed (.ok ⟨.error (invalidException s), [], after, anchors⟩) finalUsed resumes) := by
  obtain ⟨after, _, kept, advanced⟩ := ran.scalar_isolated source physical rename layout.layout noGrowth anchors
  have rejected := rejected_attempt (setLocal env "attempt" (text s)) after s (by simp [setLocal]) invalid
    (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following) anchors stack
  have failed := completion_of_heap (choices := choices) (used := finalUsed) (finishes_extend rejected extension)
    (by intro completion same; cases same; simp [invalidException]) resumes
  refine ⟨after, kept address _ layout, (advanced (validationIteratorLoop env following stack) resumes).trans ?_⟩
  simpa only [loopCode, validationIteratorLoop, Calls.loopContinuation,
    show Calls.loopControl validationBody = false from rfl, Bool.false_eq_true, ↓reduceIte,
    List.append_assoc, List.singleton_append] using failed

theorem reject_after_iterator_prefix (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (logical middle yielded : Mutable.Heap) (used nextUsed finalUsed : Nat)
    (attempts : List String) (s : String)
    (trace : YieldPrefix context choices iterator text logical used attempts middle nextUsed)
    (ran : NextRun context choices iterator middle nextUsed (.ok (text s)) yielded finalUsed)
    (noGrowth : yielded.length = logical.length)
    (valid : ∀ value ∈ attempts, value.length = 3 ∧ Strings.isDigit value = true)
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false)
    (physical : Mutable.Heap) (rename : Nat → Nat) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after, PrivateLayout yielded after rename address (.list ((checked ++ attempts).map text)) ∧
      IteratorCalls.Reaches context anchors choices []
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          env, stack, physical⟩, used⟩ resumes)
        (.completed (.ok ⟨.error (invalidException s), [], after, anchors⟩) finalUsed resumes) := by
  obtain ⟨middleClosed, prefixGrows⟩ := trace.effects source layout.layout.closed
  have lastGrows := (ran.effects source middleClosed).2
  obtain ⟨middlePhysical, nextEnv, nextPrivate, _, accepted⟩ :=
    validated_iterator_prefix context extension source choices iterator logical middle used nextUsed attempts
      trace (by omega) valid physical rename address checked env layout getChecked following anchors stack resumes
  obtain ⟨after, finalPrivate, failed⟩ := iterator_rejected_from_logical context extension source choices
    iterator middle yielded middlePhysical nextUsed finalUsed anchors s invalid ran (by omega) rename
      address (checked ++ attempts) nextPrivate nextEnv following stack resumes
  exact ⟨after, finalPrivate, accepted.trans failed⟩

end data.«project-euler-statements».data.py.project_euler_statements.p79
