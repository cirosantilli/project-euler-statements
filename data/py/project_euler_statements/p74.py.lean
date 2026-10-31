import data.«project-euler-statements».data.py.project_euler_statements.«p74.source»

/-! Public termination and execution coverage follow from the complete source-body proofs. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p74
open FormalSW.PyAst
set_option Elab.async false

theorem next_term.«Returns» (n : Int)
    (condition : Calls.Condition program
      (fun key => if key = "n" then some (.int n) else none) P74Ast.requires_next_term_0) :
    (HeapCalls.scalarFunction program "next_term" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  simpa only [Int.toNat_of_nonneg nonnegative] using
    (next_term.result n.toNat []).scalar_returns (values := [.int (n.toNat : Int)])

theorem next_term.«Supported» (n : Int)
    (condition : Calls.Condition program
      (fun key => if key = "n" then some (.int n) else none) P74Ast.requires_next_term_0) :
    (HeapCalls.scalarFunction program "next_term" [.int n]).Supported :=
  (next_term.«Returns» n condition).supported

theorem chain_len.«Returns» (n : Int)
    (condition : Calls.Condition program
      (fun key => if key = "n" then some (.int n) else none) P74Ast.requires_chain_len_0) :
    (HeapCalls.scalarFunction program "chain_len" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  obtain ⟨_, returned⟩ := chain_len.result n.toNat []
  simpa only [Int.toNat_of_nonneg nonnegative] using
    returned.scalar_returns (values := [.int (n.toNat : Int)])

theorem chain_len.«Supported» (n : Int)
    (condition : Calls.Condition program
      (fun key => if key = "n" then some (.int n) else none) P74Ast.requires_chain_len_0) :
    (HeapCalls.scalarFunction program "chain_len" [.int n]).Supported :=
  (chain_len.«Returns» n condition).supported

theorem naive.«Returns» (limit target : Int) :
    (HeapCalls.scalarFunction program "naive" [.int limit, .int target]).Returns := by
  obtain ⟨_, returned⟩ := naive.result limit target []
  exact returned.scalar_returns (values := [.int limit, .int target])

theorem naive.«Supported» (limit target : Int) :
    (HeapCalls.scalarFunction program "naive" [.int limit, .int target]).Supported :=
  (naive.«Returns» limit target).supported

end data.«project-euler-statements».data.py.project_euler_statements.p74
