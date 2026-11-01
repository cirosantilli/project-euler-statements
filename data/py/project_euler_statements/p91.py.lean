import data.«project-euler-statements».data.py.project_euler_statements.«p91.py.lean.d».Predicate

namespace data.«project-euler-statements».data.py.project_euler_statements.p91.is_right
open FormalSW.PyAst

theorem «Returns» (a b c d : Int) :
    (Calls.function P91Ast.module "is_right" [.int a, .int b, .int c, .int d]).Returns :=
  (result a b c d).returns

theorem «Supported» (a b c d : Int) :
    (Calls.function P91Ast.module "is_right" [.int a, .int b, .int c, .int d]).Supported :=
  («Returns» a b c d).supported

end data.«project-euler-statements».data.py.project_euler_statements.p91.is_right
