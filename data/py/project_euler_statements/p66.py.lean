import data.«project-euler-statements».data.py.project_euler_statements.«p66.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p66.naive
open FormalSW.PyAst
set_option Elab.async false

theorem «Returns» (limit : Int) : (Calls.function P66Ast.module "naive" [.int limit]).Returns :=
  (result limit).returns

theorem «Supported» (limit : Int) : (Calls.function P66Ast.module "naive" [.int limit]).Supported :=
  («Returns» limit).supported

end data.«project-euler-statements».data.py.project_euler_statements.p66.naive
