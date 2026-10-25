import data.«project-euler-statements».data.py.project_euler_statements.«p37.search.source»
import ProjectEulerStatements.Lib.TruncatablePrimeDecimal

namespace data.«project-euler-statements».data.py.project_euler_statements.p37
open FormalSW.PyAst ProjectEulerStatements.TruncatablePrimeBase
private abbrev program := P37Ast.module
private abbrev inputEnv (base : Int) : ScalarEnv :=
  fun name => if name = "base" then some (.int base) else none

namespace naive
theorem supported (base : Int)
    (condition : Calls.Condition program (inputEnv base) P37Ast.requires_naive_0) :
    (HeapCalls.scalarFunction program "naive" [.int base]).Supported := by
  have valid : 2 ≤ base := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift base to Nat using (by omega : 0 ≤ base)
  exact supported_base base (by omega)

theorem «Supported» (base : Int)
    (condition : Calls.Condition program (inputEnv base) P37Ast.requires_naive_0) :
    (HeapCalls.scalarFunction program "naive" [.int base]).Supported := supported base condition

theorem default_result (heap : Mutable.Heap) :
    ∃ finalHeap, HeapCalls.ReturnsValue program "naive" [] heap (.scalar (.int 748317)) finalHeap := by
  obtain ⟨finalHeap, returned⟩ := result 10 (by decide) ⟨8, Decimal.exhausted⟩ heap
  rw [Decimal.answer_default] at returned
  exact ⟨finalHeap, HeapCalls.ReturnsValue.with_defaults rfl rfl rfl returned⟩

theorem default_returns : (HeapCalls.scalarFunction program "naive" []).Returns := by
  obtain ⟨_, returned⟩ := default_result []
  exact returned.scalar_returns (values := [])
end naive

theorem naive_default.result (heap : Mutable.Heap) :
    ∃ finalHeap, HeapCalls.ReturnsValue program "naive_default" [] heap
      (.scalar (.int 748317)) finalHeap := by
  obtain ⟨finalHeap, returned⟩ := naive.default_result heap
  refine ⟨finalHeap, ?_⟩
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.call .nil returned

end data.«project-euler-statements».data.py.project_euler_statements.p37
