import data.«project-euler-statements».data.py.project_euler_statements.«p72.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p72
open FormalSW.PyAst
set_option Elab.async false

theorem count_reduced.«Returns» (d : Int) :
    (Calls.function program "count_reduced" [.int d]).Returns :=
  (count_reduced.result d).returns

theorem count_reduced.«Supported» (d : Int) :
    (Calls.function program "count_reduced" [.int d]).Supported :=
  (count_reduced.«Returns» d).supported

theorem naive.«Returns» (limit : Int) : (Calls.function program "naive" [.int limit]).Returns :=
  (naive.result limit).returns

theorem naive.«Supported» (limit : Int) : (Calls.function program "naive" [.int limit]).Supported :=
  (naive.«Returns» limit).supported

end data.«project-euler-statements».data.py.project_euler_statements.p72
