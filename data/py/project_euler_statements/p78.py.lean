import data.«project-euler-statements».data.py.project_euler_statements.«p78.search.source»

/-! Termination and source coverage for arbitrary nonnegative partition arguments. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p78
open FormalSW.PyAst
set_option Elab.async false

theorem partition_go.«Returns» (n max_ : Int)
    (first : Calls.Condition program
      (fun key => if key = "n" then some (.int n) else none) P78Ast.requires_partition_go_0)
    (second : Calls.Condition program
      (fun key => if key = "max_" then some (.int max_) else none) P78Ast.requires_partition_go_1) :
    (MemoCalls.sourceFunction program "partition_go" [.int n, .int max_]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare first rfl
  have maxNonnegative : 0 ≤ max_ := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare second rfl
  exact (partition_go.result n max_ nonnegative maxNonnegative).returns

theorem partition_go.«Supported» (n max_ : Int)
    (first : Calls.Condition program
      (fun key => if key = "n" then some (.int n) else none) P78Ast.requires_partition_go_0)
    (second : Calls.Condition program
      (fun key => if key = "max_" then some (.int max_) else none) P78Ast.requires_partition_go_1) :
    (MemoCalls.sourceFunction program "partition_go" [.int n, .int max_]).Supported :=
  (partition_go.«Returns» n max_ first second).supported

theorem partition.«Returns» (n : Int)
    (condition : Calls.Condition program
      (fun key => if key = "n" then some (.int n) else none) P78Ast.requires_partition_0) :
    (MemoCalls.sourceFunction program "partition" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  simpa only [Int.toNat_of_nonneg nonnegative] using
    (partition.result n.toNat).returns

theorem partition.«Supported» (n : Int)
    (condition : Calls.Condition program
      (fun key => if key = "n" then some (.int n) else none) P78Ast.requires_partition_0) :
    (MemoCalls.sourceFunction program "partition" [.int n]).Supported :=
  (partition.«Returns» n condition).supported

theorem naive.supported_positive (modulus : Int) (positive : 0 < modulus) :
    (MemoCalls.sourceFunction program "naive" [.int modulus]).Supported := by
  classical
  by_cases success : ProjectEulerStatements.PartitionSearch.Success modulus
  · exact (naive.result modulus positive success).returns.supported
  · exact (naive.diverges modulus positive success).supported

end data.«project-euler-statements».data.py.project_euler_statements.p78
