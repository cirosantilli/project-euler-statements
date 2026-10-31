import data.«project-euler-statements».data.py.project_euler_statements.«p75.source»

/-! Both reference functions terminate and execute supported source code at every signed input. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p75
open FormalSW.PyAst
set_option Elab.async false

theorem count_solutions.«Returns» (p : Int) :
    (HeapCalls.scalarFunction program "count_solutions" [.int p]).Returns :=
  (count_solutions.result p []).scalar_returns (values := [.int p])

theorem count_solutions.«Supported» (p : Int) :
    (HeapCalls.scalarFunction program "count_solutions" [.int p]).Supported :=
  (count_solutions.«Returns» p).supported

theorem naive.«Returns» (limit : Int) :
    (HeapCalls.scalarFunction program "naive" [.int limit]).Returns :=
  (naive.result limit []).scalar_returns (values := [.int limit])

theorem naive.«Supported» (limit : Int) :
    (HeapCalls.scalarFunction program "naive" [.int limit]).Supported :=
  (naive.«Returns» limit).supported

end data.«project-euler-statements».data.py.project_euler_statements.p75
