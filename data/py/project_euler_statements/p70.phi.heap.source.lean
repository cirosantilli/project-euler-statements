import data.«project-euler-statements».data.py.project_euler_statements.«p70.phi.source»
import lang.py.FormalSW.SumCalls

/-! The totient generator counts without allocating or changing any caller heap. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p70
open FormalSW.PyAst HeapCalls
set_option Elab.async false

abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
def numbers (values : List Int) : List Mutable.Value := values.map number

namespace heapPhi
abbrev countBody : List Stmt :=
  comprehensionFilters [gcdCondition] (sumBody (.constant (.int 1)) [])

theorem gcd_result (n k : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getK : env "k" = some (number k)) :
    HeapCalls.Evaluates program env gcdCondition heap
      (flag (decide (Nat.gcd k n = 1))) heap := by
  apply HeapCalls.Evaluates.compare (av := number (Nat.gcd k n)) (bv := number 1)
    (middle := heap) (afterRight := heap)
  · apply HeapCalls.Evaluates.library_call
      (.cons (HeapCalls.Evaluates.lookup getK) (.cons (HeapCalls.Evaluates.lookup getN) .nil)) rfl
    change HeapCalls.scalarResult (some (Math.gcdCall [.int k, .int n])) heap = _
    simp [Math.gcdCall_pair, HeapCalls.scalarResult]
  · exact HeapCalls.Evaluates.constant
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp]

private theorem loop (n first total : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getTotal : env sumAccumulator = some (number total)) :
    HeapCalls.BlockReturns program env
      [.rangeStepLoop "k" first (n + 1) 1 countBody [], .return (.name sumAccumulator)]
      heap (number (total + coprimeCount n first : Nat)) heap := by
  by_cases active : first ≤ n
  · let indexed := setLocal env "k" (number first)
    have indexedN : indexed "n" = some (number n) := by simpa [indexed, setLocal] using getN
    have indexedTotal : indexed sumAccumulator = some (number total) := by
      simpa [indexed, setLocal, sumAccumulator] using getTotal
    have tested := gcd_result n first heap indexed indexedN rfl
    apply HeapCalls.BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
    by_cases chosen : Nat.gcd first n = 1
    · apply HeapCalls.BlockReturns.branch (flag := true)
        (by simpa only [chosen, decide_true] using tested) rfl
      apply HeapCalls.BlockReturns.assign (value := number (total + 1)) (middle := heap)
      · exact HeapCalls.Evaluates.binary (av := number total) (bv := number 1)
          (middle := heap) (afterRight := heap)
          (HeapCalls.Evaluates.lookup indexedTotal) HeapCalls.Evaluates.constant
          (by simp [Mutable.binary, scalarBinary])
      · let updated := setLocal indexed sumAccumulator (number (total + 1))
        have continued := loop n (first + 1) (total + 1) heap updated
          (by simpa [updated, setLocal, sumAccumulator] using indexedN) rfl
        simpa only [countBody, comprehensionFilters, sumBody, List.foldr_cons, List.foldr_nil,
          Calls.loopContinuation, show Calls.loopControl countBody = false from rfl,
          Bool.false_eq_true, if_false, count_step n first active, chosen, if_true,
          Nat.cast_add, Nat.cast_one, Int.add_assoc, Int.add_comm,
          Int.add_left_comm] using continued
    · apply HeapCalls.BlockReturns.branch (flag := false)
        (by simpa only [chosen, decide_false] using tested) rfl
      have continued := loop n (first + 1) total heap indexed indexedN indexedTotal
      simpa only [countBody, comprehensionFilters, sumBody, List.foldr_cons, List.foldr_nil,
        Calls.loopContinuation, show Calls.loopControl countBody = false from rfl,
        Bool.false_eq_true, if_false, count_step n first active, chosen, if_false,
        Nat.zero_add, Nat.cast_add, Nat.cast_one] using continued
  · rw [count_done n first (by omega), Nat.add_zero]
    apply HeapCalls.BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup getTotal)
termination_by n + 1 - first
decreasing_by all_goals omega
end heapPhi

/-- Positive and zero arguments return the mathematical totient, preserving every heap object. -/
theorem phi.heap_natural_result (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "phi" [number n] heap (number n.totient) heap := by
  let entry := HeapCalls.functionEnv ((findFunctionIn program.body "phi").getD ([], [])).1
    ((findFunctionIn program.body "phi").getD ([], [])).2 [number n] []
  let bounds : List Expr := [.constant (.int 1), .binOp (.name "n") .add (.constant (.int 1))]
  let inner := setLocal
    (comprehensionEnv entry [("k", .call (.name "range") bounds, [gcdCondition])])
    sumAccumulator (number 0)
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.sum_range
  apply HeapCalls.Evaluates.sum_generator_range (values := [number 1, number (n + 1 : Nat)])
    (first := 1) (stop := (n + 1 : Nat)) (stride := 1) (middle := heap) (afterStart := heap)
    (.cons HeapCalls.Evaluates.constant (.cons
      (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant
        (by simp [Mutable.binary, scalarBinary])) .nil)) rfl HeapCalls.Evaluates.constant rfl
  have counted := heapPhi.loop n 1 0 heap inner
    (by simp [inner, comprehensionEnv, setLocal, sumAccumulator]; rfl) rfl
  have count : coprimeCount n 1 = n.totient := ProjectEulerStatements.P69.phi_eq_totient n
  simpa only [heapPhi.countBody, inner, count, Nat.zero_add, Nat.cast_add,
    Nat.cast_one] using counted

/-- Negative bounds exhaust an empty range and return zero without changing the heap. -/
theorem phi.heap_result (n : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "phi" [number n] heap (number n.toNat.totient) heap := by
  by_cases negative : n < 0
  · have zero : n.toNat = 0 := by omega
    rw [zero, Nat.totient_zero]
    apply HeapCalls.BlockReturns.function rfl rfl
    apply HeapCalls.BlockReturns.return_value
    apply HeapCalls.Evaluates.sum_range
    apply HeapCalls.Evaluates.sum_generator_range (values := [number 1, number (n + 1)])
      (first := 1) (stop := n + 1) (stride := 1) (middle := heap) (afterStart := heap)
      (.cons HeapCalls.Evaluates.constant (.cons
        (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant
          (by simp [Mutable.binary, scalarBinary])) .nil)) rfl HeapCalls.Evaluates.constant rfl
    apply HeapCalls.BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup (by simp [setLocal]))
  · have cast : (n.toNat : Int) = n := Int.toNat_of_nonneg (by omega)
    simpa only [cast] using phi.heap_natural_result n.toNat heap

end data.«project-euler-statements».data.py.project_euler_statements.p70
