import data.«project-euler-statements».data.py.project_euler_statements.«p64.period.source»
import ProjectEulerSolutions.Lib.SqrtPeriodCounts
import lang.py.FormalSW.SumCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p64.naive
open FormalSW.PyAst HeapCalls ProjectEulerStatements.SqrtReducedStates ProjectEulerSolutions.SqrtPeriodCounts
set_option Elab.async false
private abbrev program := P64Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
variable {globals : Mutable.Globals}

def test : Expr := .compare (.binOp (.call (.name "period_len_full") [.name "n"]) .mod (.constant (.int 2)))
  [(.eq, .constant (.int 1))]
def loopBody : List Stmt := comprehensionFilters [test] (sumBody (.constant (.int 1)) [])

theorem test_evaluates (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) :
    ∃ finalHeap, Evaluates program env test heap (flag (decide (length n % 2 = 1))) finalHeap globals := by
  obtain ⟨finalHeap, returned⟩ := period_len_full.result n heap globals
  refine ⟨finalHeap, ?_⟩
  apply Evaluates.compare (av := number ((length n % 2 : Nat) : Int)) (bv := number 1)
    (middle := finalHeap) (afterRight := finalHeap)
  · exact Evaluates.binary (av := number (length n)) (bv := number 2)
      (middle := finalHeap) (afterRight := finalHeap)
      (Evaluates.call (.cons (Evaluates.lookup getN) .nil) returned) Evaluates.constant
      (by simp [Mutable.binary, scalarBinary, number])
  · exact Evaluates.constant
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]
    norm_cast

theorem loop_result (stop : Int) (first size total : Nat) (window : (stop - first).toNat = size)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (getTotal : env sumAccumulator = some (number total)) :
    ∃ finalHeap, BlockReturns program env
      [.rangeStepLoop "n" first stop 1 loopBody [], .return (.name sumAccumulator)]
      heap (number ((total + count first size : Nat) : Int)) finalHeap globals := by
  induction size generalizing first total heap env with
  | zero =>
      refine ⟨heap, ?_⟩
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (by simpa using Evaluates.lookup getTotal)
  | succ size ih =>
      let entered := setLocal env "n" (number first)
      have keptTotal : entered sumAccumulator = some (number total) := by simpa [entered, setLocal, sumAccumulator] using getTotal
      obtain ⟨middle, tested⟩ := test_evaluates first heap entered (by simp [entered, setLocal])
      by_cases odd : length first % 2 = 1
      · obtain ⟨finalHeap, rest⟩ := ih (first + 1) (total + 1) (by omega) middle
          (setLocal entered sumAccumulator (number ((total + 1 : Nat) : Int))) (by simp [setLocal])
        refine ⟨finalHeap, ?_⟩
        apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
        apply BlockReturns.branch (flag := true) (by simpa only [odd, decide_true] using tested) rfl
        apply BlockReturns.assign (value := number ((total + 1 : Nat) : Int)) (middle := middle)
          (Evaluates.binary (av := number total) (bv := number 1) (middle := middle) (afterRight := middle)
            (Evaluates.lookup keptTotal) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number]))
        have tally : total + count first (size + 1) = total + 1 + count (first + 1) size := by
          rw [count_succ]
          simp only [weight, if_pos odd, Nat.add_assoc]
        simpa only [Calls.loopContinuation, show Calls.loopControl loopBody = false from rfl,
          Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one, tally] using rest
      · obtain ⟨finalHeap, rest⟩ := ih (first + 1) total (by omega) middle entered keptTotal
        refine ⟨finalHeap, ?_⟩
        apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
        apply BlockReturns.branch (flag := false) (by simpa only [odd, decide_false] using tested) rfl
        have tally : total + count first (size + 1) = total + count (first + 1) size := by
          rw [count_succ]
          simp only [weight, if_neg odd, Nat.zero_add]
        simpa only [Calls.loopContinuation, show Calls.loopControl loopBody = false from rfl,
          Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one, tally] using rest

theorem result (limit : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ finalHeap, ReturnsValue program "naive" [number limit] heap (number (answer limit)) finalHeap globals := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let body := ((findFunctionIn program.body "naive").getD ([], [])).2
  let env := functionEnv args body [number limit] globals
  let bounds : List Expr := [.binOp (.name "limit") .add (.constant (.int 1))]
  let summed := setLocal (comprehensionEnv env [("n", .call (.name "range") bounds, [test])]) sumAccumulator (number 0)
  obtain ⟨finalHeap, executed⟩ := loop_result (globals := globals) (limit + 1) 0 (limit + 1).toNat 0
    (by omega) heap summed (by simp [summed, setLocal])
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range (values := [number (limit + 1)]) (middle := heap)
    (.cons (Evaluates.binary (av := number limit) (bv := number 1) (middle := heap) (afterRight := heap)
      (Evaluates.lookup (by cases globals <;> rfl)) Evaluates.constant
      (by simp [Mutable.binary, scalarBinary, number])) .nil) rfl Evaluates.constant rfl
  simpa only [Nat.zero_add, reference_window] using executed

end data.«project-euler-statements».data.py.project_euler_statements.p64.naive
