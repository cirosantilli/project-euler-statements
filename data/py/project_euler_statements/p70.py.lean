import data.«project-euler-statements».data.py.project_euler_statements.«p70.phi.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p70
open FormalSW.PyAst
set_option Elab.async false

theorem phi.«Returns» (n : Int) : (Calls.function program "phi" [.int n]).Returns :=
  (phi.result n).returns

theorem phi.«Supported» (n : Int) : (Calls.function program "phi" [.int n]).Supported :=
  (phi.«Returns» n).supported

end data.«project-euler-statements».data.py.project_euler_statements.p70
