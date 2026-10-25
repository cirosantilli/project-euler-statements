import data.«project-euler-statements».data.py.project_euler_statements.«p63.seeds.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p63.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.PowerfulDigits
private abbrev program := P63Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
variable {globals : Mutable.Globals}

def exponentCondition : Expr :=
  .compare (.call (.name "num_digits")
    [.binOp (.binOp (.name "base") .sub (.constant (.int 1))) .pow (.name "n"), .name "base"])
    [(.gtE, .name "n")]
def rowStmt : Stmt :=
  .forIn (.name "a") (.call (.name "range") [.constant (.int 1), .name "base"]) seedBody []
def exponentBody : List Stmt := [rowStmt, .augAssign (.name "n") .add (.constant (.int 1))]
def exponentLoop : Stmt := .whileDo exponentCondition exponentBody []

/-- The maximal seed detects the first empty width, after which every width is empty. -/
theorem exponent_loop (base exponent total : Nat) (valid : 2 ≤ base) (positive : 1 ≤ exponent)
    (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getBase : env "base" = some (number base)) (getN : env "n" = some (number exponent))
    (getTotal : env "total" = some (number total)) :
    ∃ finalHeap, BlockReturns program env [exponentLoop, .return (.name "total")]
      heap (number (total + sumWindow (exponentCount base) exponent (bound base - exponent))) finalHeap globals := by
  let testedHeap := heap ++ [.list ((Nat.digits base ((base - 1) ^ exponent)).map number)]
  have tested : Evaluates program env exponentCondition heap
      (flag (decide (base ^ (exponent - 1) ≤ (base - 1) ^ exponent))) testedHeap globals := by
    apply Evaluates.compare (av := number (width base ((base - 1) ^ exponent)))
      (bv := number exponent) (middle := testedHeap) (afterRight := testedHeap)
    · apply Evaluates.call (values := [number ((base - 1) ^ exponent), number base]) (middle := heap)
      · refine .cons ?_ (.cons (Evaluates.lookup getBase) .nil)
        apply power_evaluates (base - 1) exponent _ _ heap env _ (Evaluates.lookup getN)
        apply Evaluates.binary (Evaluates.lookup getBase) Evaluates.constant
        have cast : ((base - 1 : Nat) : Int) = (base : Int) - 1 := by omega
        simp [Mutable.binary, scalarBinary, cast]
      · exact num_digits.result ((base - 1) ^ exponent) base valid heap globals
    · exact Evaluates.lookup getN
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag,
        width_at_least base ((base - 1) ^ exponent) exponent valid positive]
  by_cases yes : base ^ (exponent - 1) ≤ (base - 1) ^ exponent
  · have before := successful_before_bound base (base - 1) exponent valid (by omega) yes
    obtain ⟨rowEnv, rowHeap, rowRun, rowBase, rowN, rowTotal⟩ :=
      seed_loop (globals := globals) base exponent 1 (base - 1) total valid positive (by omega)
        testedHeap env getBase getN getTotal
    have row : BlockContinues program env [rowStmt] testedHeap rowEnv rowHeap globals := by
      exact BlockContinues.for_range (.cons Evaluates.constant (.cons (Evaluates.lookup getBase) .nil)) rfl rowRun
    let advanced := setLocal rowEnv "n" (number (exponent + 1))
    obtain ⟨finalHeap, rest⟩ := exponent_loop base (exponent + 1) (total + exponentCount base exponent)
      valid (by omega) rowHeap advanced
      (by simpa [advanced, setLocal] using rowBase) (by simp [advanced, setLocal])
      (by simpa only [advanced, setLocal, show "total" ≠ "n" from by decide,
        if_false, exponent_window] using rowTotal)
    refine ⟨finalHeap, ?_⟩
    have tally : total + sumWindow (exponentCount base) exponent (bound base - exponent) =
        total + exponentCount base exponent +
          sumWindow (exponentCount base) (exponent + 1) (bound base - (exponent + 1)) := by
      rw [window_tail_step _ base exponent before, Nat.add_assoc]
    apply BlockReturns.while_loop (flag := true) (by simpa only [yes, decide_true] using tested) rfl
    have advancedRun : BlockReturns program rowEnv
        [.augAssign (.name "n") .add (.constant (.int 1)), exponentLoop, .return (.name "total")]
        rowHeap (number (total + sumWindow (exponentCount base) exponent (bound base - exponent))) finalHeap globals := by
      apply BlockReturns.augAssign rowN Evaluates.constant
        (value := number (exponent + 1)) (middle := rowHeap) (afterOperation := rowHeap)
        (by simp [inplace, Mutable.binary, scalarBinary, number])
      simpa only [tally] using rest
    simpa only [exponentBody, Calls.loopContinuation, show Calls.loopControl exponentBody = false from rfl,
      Bool.false_eq_true, if_false] using row.returns advancedRun
  · have zero := exponent_window_zero base exponent (bound base - exponent) valid positive (by omega)
    refine ⟨testedHeap, ?_⟩
    apply BlockReturns.while_loop (flag := false) (by simpa only [yes, decide_false] using tested) rfl
    simpa only [zero, Nat.add_zero] using
      (BlockReturns.return_value (module := program) (heap := testedHeap) (Evaluates.lookup getTotal))
termination_by bound base - exponent
decreasing_by omega

theorem body_result (base : Nat) (valid : 2 ≤ base) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getBase : env "base" = some (number base)) :
    ∃ finalHeap, BlockReturns program env
      (executableBody ((findFunctionIn program.body "naive").getD ([], [])).2)
      heap (number (answer base)) finalHeap globals := by
  obtain ⟨finalHeap, executed⟩ := exponent_loop base 1 0 valid (by omega) heap
    (setLocal (setLocal env "total" (number 0)) "n" (number 1))
    (by simpa [setLocal] using getBase) (by simp [setLocal]) (by simp [setLocal])
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.assign Evaluates.constant
  simpa only [exponent_sum, Nat.zero_add] using executed

theorem result (base : Nat) (valid : 2 ≤ base) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ finalHeap, ReturnsValue program "naive" [number base] heap (number (answer base)) finalHeap globals := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let body := ((findFunctionIn program.body "naive").getD ([], [])).2
  obtain ⟨finalHeap, executed⟩ := body_result base valid heap (functionEnv args body [number base] globals)
    (by cases globals <;> rfl)
  exact ⟨finalHeap, BlockReturns.function rfl rfl executed⟩

end data.«project-euler-statements».data.py.project_euler_statements.p63.naive
