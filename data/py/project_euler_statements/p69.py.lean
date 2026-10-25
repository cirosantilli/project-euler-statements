import data.«project-euler-statements».data.py.project_euler_statements.«p69.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p69
open FormalSW.PyAst
set_option Elab.async false

theorem phi.«Returns» (n : Int) : (Calls.function program "phi" [.int n]).Returns :=
  (phi.result n).returns

theorem phi.«Supported» (n : Int) : (Calls.function program "phi" [.int n]).Supported :=
  (phi.«Returns» n).supported

theorem naive.«Returns» (limit : Int) : (Calls.function program "naive" [.int limit]).Returns :=
  (naive.result limit).returns

theorem naive.«Supported» (limit : Int) : (Calls.function program "naive" [.int limit]).Supported :=
  (naive.«Returns» limit).supported

end data.«project-euler-statements».data.py.project_euler_statements.p69
