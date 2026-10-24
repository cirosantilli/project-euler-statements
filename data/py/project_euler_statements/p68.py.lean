import data.«project-euler-statements».data.py.project_euler_statements.«p68.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p68.naive
open FormalSW.PyAst
set_option Elab.async false

theorem «Returns» (n digits : Int) :
    (HeapCalls.scalarFunction program "naive" [.int n, .int digits]).Returns := by
  obtain ⟨_, executed⟩ := full_result n digits []
  exact executed.scalar_returns (values := [.int n, .int digits])

theorem «Supported» (n digits : Int) :
    (HeapCalls.scalarFunction program "naive" [.int n, .int digits]).Supported :=
  («Returns» n digits).supported

theorem one_argument_returns (n : Int) :
    (HeapCalls.scalarFunction program "naive" [.int n]).Returns := by
  obtain ⟨_, executed⟩ := one_argument_result n []
  exact executed.scalar_returns (values := [.int n])

theorem default_returns : (HeapCalls.scalarFunction program "naive" []).Returns := by
  obtain ⟨_, executed⟩ := default_result []
  exact executed.scalar_returns (values := [])

end data.«project-euler-statements».data.py.project_euler_statements.p68.naive
