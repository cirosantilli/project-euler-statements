import data.«project-euler-statements».data.py.project_euler_statements.«p37.predicate.source»
import ProjectEulerSolutions.Lib.TruncatablePrimeSearch

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p37.naive
open FormalSW.PyAst HeapCalls ProjectEulerStatements.TruncatablePrimeBase
open ProjectEulerSolutions.TruncatablePrimeCalls
private abbrev program := P37Ast.module

private theorem prime_result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "is_prime" [number n] heap (flag (decide (Nat.Prime n))) heap :=
  (common.is_prime.heap_result n heap).extend common_extension

private theorem predicate_result (radix : Nat) (valid : 2 ≤ radix)
    (n : Nat) (large : radix ≤ n) (right : RightPrime radix n) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "is_truncatable_prime" [number n, number radix] heap
      (flag (leftCheck radix n)) (heap ++ extra) := by
  obtain ⟨extra, checked⟩ := is_truncatable_prime.result radix n valid heap
  have prime := right_prime radix n (by omega) right
  have same : referenceCheck radix n = leftCheck radix n := by
    simp only [referenceCheck, large, decide_true, prime, Bool.true_and]
    exact digitCheck_of_rightPrime radix n valid (by omega) right
  exact ⟨extra, same ▸ checked⟩

theorem result (radix : Nat) (valid : 2 ≤ radix) (success : Exhausts radix) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive" [number radix] heap
      (number (answer radix success)) finalHeap :=
  function_result program radix "is_truncatable_prime" valid prime_result (predicate_result radix valid)
    "naive" ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 rfl rfl rfl rfl success heap

theorem diverges (radix : Nat) (valid : 2 ≤ radix) (absent : ¬ Exhausts radix) :
    (HeapCalls.scalarFunction program "naive" [.int radix]).Diverges :=
  function_diverges program radix "is_truncatable_prime" valid prime_result (predicate_result radix valid)
    "naive" ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 rfl rfl rfl rfl absent

theorem returns_iff (radix : Nat) (valid : 2 ≤ radix) :
    (HeapCalls.scalarFunction program "naive" [.int radix]).Returns ↔ Exhausts radix := by
  constructor
  · rintro ⟨value, returned⟩
    by_contra absent
    exact Execution.diverges_not_halts (diverges radix valid absent) ⟨.ok value, returned⟩
  · intro success
    obtain ⟨_, returned⟩ := result radix valid success []
    exact returned.scalar_returns (values := [.int radix])

theorem supported_base (radix : Nat) (valid : 2 ≤ radix) :
    (HeapCalls.scalarFunction program "naive" [.int radix]).Supported := by
  classical
  by_cases success : Exhausts radix
  · exact ((returns_iff radix valid).mpr success).supported
  · exact (diverges radix valid success).supported

end data.«project-euler-statements».data.py.project_euler_statements.p37.naive
