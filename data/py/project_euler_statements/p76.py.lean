import data.«project-euler-statements».data.py.project_euler_statements.«p76.source»

/-! Both partition reference functions terminate for all signed integer arguments. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p76
open FormalSW.PyAst FormalSW.PyAst.MemoCalls
set_option Elab.async false

theorem count_ways.«Returns» (n max_ : Int) :
    (sourceFunction program "count_ways" [.int n, .int max_]).Returns :=
  (count_ways.result n max_).returns

theorem count_ways.«Supported» (n max_ : Int) :
    (sourceFunction program "count_ways" [.int n, .int max_]).Supported :=
  (count_ways.«Returns» n max_).supported

theorem naive.«Returns» (n : Int) : (sourceFunction program "naive" [.int n]).Returns :=
  (naive.result n).returns

theorem naive.«Supported» (n : Int) : (sourceFunction program "naive" [.int n]).Supported :=
  (naive.«Returns» n).supported

end data.«project-euler-statements».data.py.project_euler_statements.p76
