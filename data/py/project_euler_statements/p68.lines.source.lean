import data.«project-euler-statements».data.py.project_euler_statements.«p68.text.source»
import ProjectEulerStatements.Lib.MagicRingLineCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p68
open FormalSW.PyAst HeapCalls ProjectEulerStatements MagicRingTextCalls MagicRingLineCalls
set_option Elab.async false

private abbrev naiveCode : List Stmt :=
  ((findFunctionIn program.body "naive").getD ([], [])).2
private abbrev permutationBody : List Stmt :=
  match (naiveCode[2]? : Option Stmt) with
  | some (Stmt.forIn _ _ instructions _) => instructions
  | _ => []
abbrev lineLoop : Stmt := permutationBody[5]'(by decide)

theorem line_loop_source : lineLoop =
    .forIn (.name "index") (.call (.name "range") [.constant (.int 1), .name "n"])
      MagicRingLineCalls.body [] := rfl

theorem lines.result {n : Nat} (ring : MagicRing.Ring n) (target : Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (outerAddress innerAddress : Nat)
    (getOuter : heap[outerAddress]? = some (.list (encode ring.outer)))
    (getInner : heap[innerAddress]? = some (.tuple (encode ring.inner)))
    (ready : MagicRingLineCalls.Ready n target outerAddress innerAddress env) :
    ∃ finalEnv, BlockContinues program env [lineLoop] heap finalEnv heap ∧
      finalEnv "magic" = some (.scalar (.bool (checks ring target 1))) ∧ Keeps env finalEnv := by
  obtain ⟨finalEnv, checked, magic, kept⟩ := MagicRingLineCalls.loop_result program ring target 1
    heap env outerAddress innerAddress getOuter getInner ready
  refine ⟨finalEnv, ?_, magic, kept⟩
  rw [line_loop_source]
  exact BlockContinues.for_range
    (.cons Evaluates.constant (.cons (Evaluates.lookup ready.getN) .nil)) rfl checked

end data.«project-euler-statements».data.py.project_euler_statements.p68
