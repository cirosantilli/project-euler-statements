import data.«project-euler-statements».data.py.project_euler_statements.«p69.better.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p69
open FormalSW.PyAst Calls ProjectEulerStatements TotientMaximum
set_option Elab.async false

abbrev naiveArgs : List Arg := ((findFunctionIn program.body "naive").getD ([], [])).1
abbrev naiveBody : List Stmt := ((findFunctionIn program.body "naive").getD ([], [])).2
abbrev loopBody : List Stmt :=
  [.ifThen (.call (.name "better") [.name "n", .name "best"])
    [.assign [.name "best"] (.name "n")] []]

theorem naive_function_source : findFunctionIn program.body "naive" =
    some (naiveArgs, naiveBody) := rfl

theorem naive_code_source : executableBody naiveBody =
    [.assign [.name "best"] (.constant (.int 1)),
     .forIn (.name "n") (.call (.name "range")
       [.binOp (.name "limit") .add (.constant (.int 1))]) loopBody [],
     .return (.name "best")] := rfl

theorem loop_result (first count stop : Nat) (length : first + count = stop)
    (best : Nat) (env : ScalarEnv) (getBest : env "best" = some (.int best)) :
    BlockReturns program env
      [.rangeStepLoop "n" first stop 1 loopBody [], .return (.name "best")]
      (.int ((List.range' first count).foldl visit best : Nat)) := by
  induction count generalizing first best env with
  | zero =>
      simp only [List.range'_zero, List.foldl_nil]
      apply BlockReturns.range_done (by simp [rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getBest)
  | succ count ih =>
      let indexed := env.set "n" (.int first)
      have compared : Evaluates program indexed (.call (.name "better") [.name "n", .name "best"])
          (.bool (TotientMaximum.better first best)) :=
        Evaluates.call
          (.cons (Evaluates.lookup (by simp [indexed, ScalarEnv.set]))
            (.cons (Evaluates.lookup (by simpa [indexed, ScalarEnv.set] using getBest)) .nil))
          (better.result first best)
      apply BlockReturns.range_step (by simp [rangeContinues]; omega)
      cases chosen : TotientMaximum.better first best with
      | false =>
          apply BlockReturns.branch (by simpa only [chosen] using compared)
          have continued := ih (first + 1) (by omega) best indexed
            (by simpa [indexed, ScalarEnv.set] using getBest)
          simpa only [List.range'_succ, List.foldl_cons, visit, chosen, Bool.false_eq_true,
            if_false, Int.natCast_add, Int.natCast_one] using continued
      | true =>
          apply BlockReturns.branch (by simpa only [chosen] using compared)
          apply BlockReturns.assign (value := .int first)
            (Evaluates.lookup (by simp [ScalarEnv.set]))
          have continued := ih (first + 1) (by omega) first (indexed.set "best" (.int first))
            (by simp [ScalarEnv.set])
          simpa only [List.range'_succ, List.foldl_cons, visit, chosen, if_true,
            Int.natCast_add, Int.natCast_one] using continued

theorem naive.result (limit : Int) :
    ReturnsValue program "naive" [.int limit] (.int (referenceResult limit)) := by
  let env := (argumentEnv naiveArgs [.int limit]).set "best" (.int 1)
  apply BlockReturns.function naive_function_source rfl
  rw [naive_code_source]
  apply BlockReturns.assign Evaluates.constant
  by_cases negative : limit < 0
  · have clipped : limit.toNat = 0 := by omega
    simp only [referenceResult, clipped, bestUpTo_zero]
    apply BlockReturns.for_range (.cons
      (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil) rfl
    apply BlockReturns.range_done (by simp [rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup rfl)
  · have cast : (limit.toNat : Int) = limit := Int.toNat_of_nonneg (by omega)
    apply BlockReturns.for_range (.cons
      (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil) rfl
    have executed := loop_result 0 (limit.toNat + 1) (limit.toNat + 1) (by omega) 1 env rfl
    simpa only [← List.range_eq_range', fold_range_best, referenceResult,
      Int.natCast_zero, Int.natCast_add, Int.natCast_one, cast] using executed

end data.«project-euler-statements».data.py.project_euler_statements.p69
