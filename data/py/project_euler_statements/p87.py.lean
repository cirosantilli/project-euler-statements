import data.«project-euler-statements».data.py.project_euler_statements.«p87.py.lean.d».Execution
import lang.py.FormalSW.SetCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p87.naive
open FormalSW.PyAst
set_option Elab.async false

theorem «Returns» (limit : Int) :
    (SetCalls.call program "naive" [.scalar (.int limit)] []).Returns := by
  obtain ⟨_, returned⟩ := result limit []
  exact SetCalls.returns_of_heap returned.returns

theorem «Supported» (limit : Int) :
    (SetCalls.call program "naive" [.scalar (.int limit)] []).Supported := by
  intro choices
  exact («Returns» limit choices).supported

end data.«project-euler-statements».data.py.project_euler_statements.p87.naive
