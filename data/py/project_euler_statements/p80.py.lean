import data.«project-euler-statements».data.py.project_euler_statements.«p80.py.lean.d».Execution

namespace data.«project-euler-statements».data.py.project_euler_statements.p80.naive
open FormalSW.PyAst
set_option Elab.async false
private abbrev program := P80Ast.module
private abbrev limitCondition (limit : Int) :=
  Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none) P80Ast.requires_naive_0
private abbrev digitsCondition (digits : Int) :=
  Calls.Condition program (fun name => if name = "digits" then some (.int digits) else none) P80Ast.requires_naive_1

private theorem inputs (limit digits : Int) (bound : limitCondition limit) (precision : digitsCondition digits) :
    0 ≤ limit ∧ 0 ≤ digits := by
  have lower : 0 ≤ limit := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare bound rfl
  have positive : 1 ≤ digits := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare precision rfl
  omega

theorem «Returns» (limit digits : Int) (bound : limitCondition limit) (precision : digitsCondition digits) :
    (HeapCalls.scalarFunction program "naive" [.int limit, .int digits]).Returns := by
  obtain ⟨lower, positive⟩ := inputs limit digits bound precision
  lift limit to Nat using lower
  lift digits to Nat using positive
  obtain ⟨_, returned⟩ := result limit digits []
  exact returned.scalar_returns (values := [.int limit, .int digits])

theorem «Supported» (limit digits : Int) (bound : limitCondition limit) (precision : digitsCondition digits) :
    (HeapCalls.scalarFunction program "naive" [.int limit, .int digits]).Supported :=
  («Returns» limit digits bound precision).supported

end data.«project-euler-statements».data.py.project_euler_statements.p80.naive
