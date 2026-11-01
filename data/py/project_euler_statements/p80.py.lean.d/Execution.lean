import data.«project-euler-statements».data.py.project_euler_statements.«p80.py.lean.d».Prefix

namespace data.«project-euler-statements».data.py.project_euler_statements.p80.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.SquareRootDigitCalls
open ProjectEulerStatements
set_option Elab.async false
private abbrev program := P80Ast.module
variable {globals : Mutable.Globals}

private abbrev element : Expr := .call (.name "sqrt_digits_sum") [.name "n", .name "digits"]
private abbrev body : List Stmt := sumBody element []

theorem loop_result (stop first count precision total : Nat) (endpoint : first + count = stop)
    (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getDigits : env "digits" = some (number precision))
    (getTotal : env sumAccumulator = some (number total)) :
    ∃ extra, BlockReturns program env
      [.rangeStepLoop "n" first stop 1 body [], .return (.name sumAccumulator)] heap
      (number ((List.range' first count).foldl (fun acc n => acc + P80.sqrtDigitsSum n precision) total))
      (heap ++ extra) globals := by
  induction count generalizing first total env heap with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let entered := setLocal env "n" (number first)
      let updated := setLocal entered sumAccumulator (number (total + P80.sqrtDigitsSum first precision))
      obtain ⟨allocated, called⟩ := sqrt_digits_sum.result first precision heap globals
      obtain ⟨extra, rest⟩ := ih (first + 1) (total + P80.sqrtDigitsSum first precision)
        (by omega) (heap ++ allocated) updated
        (by simpa [updated, entered, setLocal, sumAccumulator] using getDigits) (by simp [updated, setLocal])
      refine ⟨allocated ++ extra, ?_⟩
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      apply BlockReturns.assign (value := number (total + P80.sqrtDigitsSum first precision))
        (middle := heap ++ allocated)
      · apply Evaluates.binary (av := number total) (bv := number (P80.sqrtDigitsSum first precision))
          (middle := heap) (afterRight := heap ++ allocated)
          (Evaluates.lookup (by simpa [setLocal, sumAccumulator] using getTotal))
          (Evaluates.call (.cons (Evaluates.lookup (by simp [setLocal]))
            (.cons (Evaluates.lookup (by simpa [setLocal] using getDigits)) .nil)) called)
        simp [Mutable.binary, scalarBinary, number]
      · simpa only [List.range'_succ, List.foldl_cons, body, sumBody, Calls.loopContinuation,
          show Calls.loopControl body = false from rfl, Bool.false_eq_true, if_false,
          Int.natCast_add, Int.natCast_one, List.append_assoc] using rest

theorem result (limit precision : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "naive" [number limit, number precision] heap
      (number (P80.naive limit precision)) (heap ++ extra) globals := by
  let env := functionEnv
    [{ name := "limit", annotation := some (.name "int") }, { name := "digits", annotation := some (.name "int") }]
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit, number precision] globals
  let summed := setLocal (comprehensionEnv env
    [("n", .call (.name "range") [.binOp (.name "limit") .add (.constant (.int 1))], [])])
    sumAccumulator (number 0)
  have getDigits : summed "digits" = some (number precision) := by cases globals <;> rfl
  obtain ⟨extra, loop⟩ := loop_result (globals := globals) (limit + 1) 0 (limit + 1) precision 0 (by omega)
    heap summed getDigits (by simp [summed, setLocal])
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range
    (.cons (Evaluates.binary (value := number (limit + 1)) (av := number limit) (bv := number 1)
      (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup (by cases globals <;> rfl)) Evaluates.constant
      (by simp [Mutable.binary, scalarBinary, number])) .nil)
    rfl Evaluates.constant rfl
  simpa only [P80.naive, P80.totalSum, List.range_eq_range'] using loop

end data.«project-euler-statements».data.py.project_euler_statements.p80.naive
