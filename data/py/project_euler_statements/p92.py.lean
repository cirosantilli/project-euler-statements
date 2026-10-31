import data.«project-euler-statements».data.py.project_euler_statements.«p92.py.lean.d».Counting

namespace data.«project-euler-statements».data.py.project_euler_statements.p92.next_term
open FormalSW.PyAst
set_option Elab.async false

private abbrev inputCondition (n : Int) :=
  Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
    P92Ast.requires_next_term_0

theorem «Returns» (n : Int) (valid : inputCondition n) :
    (HeapCalls.scalarFunction program "next_term" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare valid rfl
  lift n to Nat using nonnegative
  exact (result n []).scalar_returns (values := [.int n])

theorem «Supported» (n : Int) (valid : inputCondition n) :
    (HeapCalls.scalarFunction program "next_term" [.int n]).Supported :=
  («Returns» n valid).supported

end data.«project-euler-statements».data.py.project_euler_statements.p92.next_term

namespace data.«project-euler-statements».data.py.project_euler_statements.p92.ends_at_89
open FormalSW.PyAst
set_option Elab.async false

private abbrev inputCondition (n : Int) :=
  Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
    P92Ast.requires_ends_at_89_0

theorem «Returns» (n : Int) (valid : inputCondition n) :
    (HeapCalls.scalarFunction program "ends_at_89" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare valid rfl
  lift n to Nat using nonnegative
  obtain ⟨_, returned⟩ := result n []
  exact returned.scalar_returns (values := [.int n])

theorem «Supported» (n : Int) (valid : inputCondition n) :
    (HeapCalls.scalarFunction program "ends_at_89" [.int n]).Supported :=
  («Returns» n valid).supported

end data.«project-euler-statements».data.py.project_euler_statements.p92.ends_at_89

namespace data.«project-euler-statements».data.py.project_euler_statements.p92.naive
open FormalSW.PyAst

theorem «Returns» (limit_exclusive : Int) :
    (HeapCalls.scalarFunction program "naive" [.int limit_exclusive]).Returns := by
  obtain ⟨_, returned⟩ := result limit_exclusive []
  exact returned.scalar_returns (values := [.int limit_exclusive])

theorem «Supported» (limit_exclusive : Int) :
    (HeapCalls.scalarFunction program "naive" [.int limit_exclusive]).Supported :=
  («Returns» limit_exclusive).supported

end data.«project-euler-statements».data.py.project_euler_statements.p92.naive
