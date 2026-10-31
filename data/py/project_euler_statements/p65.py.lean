import data.«project-euler-statements».data.py.project_euler_statements.«p65.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p65.naive
open FormalSW.PyAst ProjectEulerSolutions.EConvergents
set_option Elab.async false
private abbrev program := P65Ast.module
private abbrev inputEnv (n : Int) : ScalarEnv := fun name => if name = "n" then some (.int n) else none

theorem «Returns» (n : Int) (condition : Calls.Condition program (inputEnv n) P65Ast.requires_naive_0) :
    (HeapCalls.scalarFunction program "naive" [.int n]).Returns := by
  have positive : 1 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift n to Nat using (by omega : 0 ≤ n)
  obtain ⟨_, returned⟩ := result n []
  exact returned.scalar_returns (values := [.int n])

theorem «Supported» (n : Int) (condition : Calls.Condition program (inputEnv n) P65Ast.requires_naive_0) :
    (HeapCalls.scalarFunction program "naive" [.int n]).Supported := («Returns» n condition).supported

theorem default_result (heap : Mutable.Heap) :
    ∃ extra, HeapCalls.ReturnsValue program "naive" [] heap (.scalar (.int (answer 100))) (heap ++ extra) := by
  obtain ⟨extra, returned⟩ := result 100 heap
  exact ⟨extra, HeapCalls.ReturnsValue.with_defaults rfl rfl rfl returned⟩

theorem default_returns : (HeapCalls.scalarFunction program "naive" []).Returns := by
  obtain ⟨_, returned⟩ := default_result []
  exact returned.scalar_returns (values := [])

end data.«project-euler-statements».data.py.project_euler_statements.p65.naive
