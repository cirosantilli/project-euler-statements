import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».Execution

namespace data.«project-euler-statements».data.py.project_euler_statements.p90
open FormalSW.PyAst

/-- Every signed count terminates for any finite list of nonnegative requirements. -/
theorem naive.«Returns» (count : Int) (required : counting.Required) (heap : Mutable.Heap)
    (globals : Mutable.Globals) (valid : required.Valid heap) :
    (HeapMemoCalls.call program "naive" [.scalar (.int count), .ref required.address] heap globals).Returns :=
  (naive.result count required heap globals valid).returns

theorem naive.«Supported» (count : Int) (required : counting.Required) (heap : Mutable.Heap)
    (globals : Mutable.Globals) (valid : required.Valid heap) :
    (HeapMemoCalls.call program "naive" [.scalar (.int count), .ref required.address] heap globals).Supported :=
  (naive.«Returns» count required heap globals valid).supported

end data.«project-euler-statements».data.py.project_euler_statements.p90
