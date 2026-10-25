import data.«project-euler-statements».data.py.project_euler_statements.«p63.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p63
open FormalSW.PyAst ProjectEulerSolutions.PowerfulDigits
private abbrev program := P63Ast.module
private abbrev inputEnv (base : Int) : ScalarEnv :=
  fun name => if name = "base" then some (.int base) else none

namespace naive
theorem «Returns» (base : Int)
    (condition : Calls.Condition program (inputEnv base) P63Ast.requires_naive_0) :
    (HeapCalls.scalarFunction program "naive" [.int base]).Returns := by
  have valid : 2 ≤ base := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift base to Nat using (by omega : 0 ≤ base)
  obtain ⟨_, returned⟩ := result base (by omega) []
  exact returned.scalar_returns (values := [.int base])

theorem «Supported» (base : Int)
    (condition : Calls.Condition program (inputEnv base) P63Ast.requires_naive_0) :
    (HeapCalls.scalarFunction program "naive" [.int base]).Supported :=
  («Returns» base condition).supported

theorem default_result (heap : Mutable.Heap) :
    ∃ finalHeap, HeapCalls.ReturnsValue program "naive" [] heap
      (.scalar (.int (answer 10))) finalHeap := by
  obtain ⟨finalHeap, returned⟩ := result 10 (by omega) heap
  exact ⟨finalHeap, HeapCalls.ReturnsValue.with_defaults rfl rfl rfl returned⟩

theorem default_returns : (HeapCalls.scalarFunction program "naive" []).Returns := by
  obtain ⟨_, returned⟩ := default_result []
  exact returned.scalar_returns (values := [])
end naive

theorem naive_default.result (heap : Mutable.Heap) :
    ∃ finalHeap, HeapCalls.ReturnsValue program "naive_default" [] heap
      (.scalar (.int (answer 10))) finalHeap := by
  obtain ⟨finalHeap, returned⟩ := naive.default_result heap
  refine ⟨finalHeap, ?_⟩
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.call .nil returned

end data.«project-euler-statements».data.py.project_euler_statements.p63
