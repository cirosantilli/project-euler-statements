import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p4.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW

namespace data.«project-euler-statements».data.py.project_euler_statements.p4
open FormalSW.PyAst

private theorem common_extension : Calls.Extends P4Ast.module CommonAst.module := by
  change Calls.Extends ⟨P4Ast.module.body.take 2 ++ CommonAst.module.body⟩ CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["naive"] at member
    have only : name = "naive" := by simpa using member
    subst name
    decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

/-- Reuse the helper's source proof in the linked problem-4 module. -/
theorem digits_result (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue P4Ast.module "digits_le" [.scalar (.int n)] heap (.ref heap.length)
      (heap ++ [(Nat.digits 10 n).map (fun (digit : Nat) => .scalar (.int (digit : Int)))]) :=
  (common.digits_le.decimal n heap).extend common_extension

end data.«project-euler-statements».data.py.project_euler_statements.p4
