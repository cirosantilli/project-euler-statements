import data.«project-euler-statements».data.py.project_euler_statements.«p86.py.lean.d».Search

namespace data.«project-euler-statements».data.py.project_euler_statements.p86.naive
open FormalSW.PyAst
set_option Elab.async false

theorem «Returns» (target : Int) :
    (Calls.function P86Ast.module "naive" [.int target]).Returns :=
  (result target).returns

theorem «Supported» (target : Int) :
    (Calls.function P86Ast.module "naive" [.int target]).Supported :=
  («Returns» target).supported

end data.«project-euler-statements».data.py.project_euler_statements.p86.naive
