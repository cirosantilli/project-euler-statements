import data.«project-euler-statements».data.py.project_euler_statements.«p85.py.lean.d».Scalar

namespace data.«project-euler-statements».data.py.project_euler_statements.p85.naive
open FormalSW.PyAst
set_option Elab.async false

theorem «Returns» (target : Int) :
    (Calls.function P85Ast.module "naive" [.int target]).Returns := by
  obtain ⟨_, _, returned⟩ := Scalar.naive_result target
  exact returned.returns

theorem «Supported» (target : Int) :
    (Calls.function P85Ast.module "naive" [.int target]).Supported :=
  («Returns» target).supported

end data.«project-euler-statements».data.py.project_euler_statements.p85.naive
