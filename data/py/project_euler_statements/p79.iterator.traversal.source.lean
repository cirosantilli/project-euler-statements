import data.«project-euler-statements».data.py.project_euler_statements.«p79.iterator.isolation.source»
import lang.py.FormalSW.IteratorTraversal

/-! Reference validation composes every valid yielded attempt and the final iterator exit. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls Mutable.Relocation IteratorCalls
set_option Elab.async false

theorem validated_iterator_traversal (context : Module) (extension : Extends context program)
    (source : IteratorCalls.Relocation.ModuleSource context) (choices : ChoiceSchedule)
    (iterator : Mutable.Value) (logical finalLogical : Mutable.Heap) (used finalUsed : Nat)
    (attempts : List String) (outcome : Except ExceptionObject Unit)
    (trace : Traversal context choices iterator text logical used attempts outcome finalLogical finalUsed)
    (noGrowth : finalLogical.length = logical.length)
    (valid : ∀ s ∈ attempts, s.length = 3 ∧ Strings.isDigit s = true)
    (physical : Mutable.Heap) (rename : Nat → Nat) (address : Nat) (checked : List String)
    (env : HeapCalls.Env) (layout : PrivateLayout logical physical rename address (.list (checked.map text)))
    (getChecked : env "checked" = some (.ref address))
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) (resumes : List Resume) :
    ∃ after finalEnv,
      PrivateLayout finalLogical after rename address (.list ((checked ++ attempts).map text)) ∧
      finalEnv "checked" = some (.ref address) ∧
      ExitResult context choices anchors
        (.running ⟨⟨.block (validationLoop (sequenceSource (relocateValue rename iterator)) 0 :: following)
          env, stack, physical⟩, used⟩ resumes)
        (validationIteratorLoop finalEnv following stack) resumes after finalUsed outcome := by
  induction trace generalizing physical checked env with
  | exhausted ran =>
      obtain ⟨after, _, kept, exited⟩ := ran.exit_isolated source physical rename layout.layout noGrowth anchors
      refine ⟨after, env, ?_, getChecked, ?_⟩
      · simpa only [List.append_nil] using kept address (.list (checked.map text)) layout
      · simpa only [exitOutcome, ↓reduceIte] using exited (validationIteratorLoop env following stack) resumes
  | failed ran notExhausted =>
      obtain ⟨after, _, kept, exited⟩ := ran.exit_isolated source physical rename layout.layout noGrowth anchors
      refine ⟨after, env, ?_, getChecked, ?_⟩
      · simpa only [List.append_nil] using kept address (.list (checked.map text)) layout
      · simpa only [exitOutcome, if_neg notExhausted] using exited (validationIteratorLoop env following stack) resumes
  | @yielded before middle after used nextUsed finalUsed s rest outcome ran later ih =>
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
      obtain ⟨result, finalEnv, retained, finalChecked, exited⟩ := ih laterSize
        (fun value member => valid value (List.mem_cons_of_mem _ member))
        _ (checked ++ [s]) (setLocal env "attempt" (text s)) fixedMap
        (by simpa [setLocal] using getChecked)
      refine ⟨result, finalEnv, ?_, finalChecked, exited.before iteration⟩
      simpa only [List.append_assoc, List.singleton_append] using retained

end data.«project-euler-statements».data.py.project_euler_statements.p79
