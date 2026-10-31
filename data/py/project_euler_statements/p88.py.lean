import data.«project-euler-statements».data.py.project_euler_statements.«p88.py.lean.d».Execution

namespace data.«project-euler-statements».data.py.project_euler_statements.p88.naive
open FormalSW.PyAst
set_option Elab.async false

theorem «Returns» (maxSize : Int) :
    (HeapCalls.scalarFunction program "naive" [.int maxSize]).Returns := by
  obtain ⟨_, returned⟩ := result maxSize []
  exact returned.scalar_returns

theorem «Supported» (maxSize : Int) :
    (HeapCalls.scalarFunction program "naive" [.int maxSize]).Supported :=
  («Returns» maxSize).supported

end data.«project-euler-statements».data.py.project_euler_statements.p88.naive
