import data.«project-euler-statements».data.py.project_euler_statements.«p79.iterator.prefix.source»

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
  obtain ⟨middle, nextUsed, error, first, last, result⟩ := trace.decompose
  obtain ⟨middleClosed, prefixGrows⟩ := first.effects source layout.layout.closed
  have lastGrows := (last.effects source middleClosed).2
  obtain ⟨middlePhysical, nextEnv, nextPrivate, nextChecked, accepted⟩ :=
    validated_iterator_prefix context extension source choices iterator logical middle used nextUsed attempts
      first (by omega) valid physical rename address checked env layout getChecked following anchors stack resumes
  obtain ⟨after, _, kept, exited⟩ := last.exit_isolated source middlePhysical rename nextPrivate.layout (by omega) anchors
  refine ⟨after, nextEnv, kept address _ nextPrivate, nextChecked, ?_⟩
  rw [← result]
  exact (exited (validationIteratorLoop nextEnv following stack) resumes).before accepted

end data.«project-euler-statements».data.py.project_euler_statements.p79
