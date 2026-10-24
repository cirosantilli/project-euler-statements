import data.«project-euler-statements».data.py.project_euler_statements.«p66.minimum.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p66.naive
open FormalSW.PyAst Calls ProjectEulerStatements.PellMinimum ProjectEulerStatements.PellSearch
set_option Elab.async false
private abbrev program := P66Ast.module
private abbrev natural (n : Nat) : Constant := .int n
private abbrev number (n : Int) : Constant := .int n
private abbrev flag (value : Bool) : Constant := .bool value

def iteration : List Stmt :=
  [.assign [.name "x"] (.call (.name "minimal_x") [.name "d"]),
   .ifThen (.compare (.name "x") [(.gt, .name "best_x")])
     [.assign [.tuple [.name "best_d", .name "best_x"]] (.tuple [.name "d", .name "x"])] []]

/-- The ascending source traversal retains the first discriminant attaining each record x. -/
theorem loop_result (stop : Int) (first size bestD bestX : Nat) (window : (stop - first).toNat = size)
    (env : ScalarEnv)
    (getBestD : env "best_d" = some (natural bestD)) (getBestX : env "best_x" = some (natural bestX)) :
    BlockReturns program env
      [.rangeStepLoop "d" first stop 1 iteration [], .return (.name "best_d")]
      (natural (scan first size bestD bestX).1) := by
  induction size generalizing first bestD bestX env with
  | zero =>
      apply BlockReturns.range_done (by simp [rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getBestD)
  | succ size ih =>
      let entered := env.set "d" (natural first)
      let ready := entered.set "x" (natural (minimum first))
      have tested : Evaluates program ready (.compare (.name "x") [(.gt, .name "best_x")])
          (flag (decide (bestX < minimum first))) := by
        apply Evaluates.compare (av := natural (minimum first)) (bv := natural bestX)
          (Evaluates.lookup (by simp [ready, ScalarEnv.set]))
          (Evaluates.lookup (by simpa [ready, entered, ScalarEnv.set] using getBestX))
        simp [scalarCompare, evalCmpOp]
      by_cases better : bestX < minimum first
      · rw [scan_succ, if_pos better]
        let pair := [natural first, natural (minimum first)]
        let improved := assignNames ready ["best_d", "best_x"] pair
        have rest := ih (first + 1) first (minimum first) (by omega) improved
          (by simp [improved, pair, assignNames, ScalarEnv.set])
          (by simp [improved, pair, assignNames, ScalarEnv.set])
        apply BlockReturns.range_step (by simp [rangeContinues]; omega)
        apply BlockReturns.assign (value := natural (minimum first))
          (Evaluates.call (.cons (Evaluates.lookup (by simp [ScalarEnv.set])) .nil) (minimal_x.result first))
        apply BlockReturns.branch (value := .bool true) (by simpa only [better, decide_true] using tested)
        apply BlockReturns.unpack (names := ["best_d", "best_x"]) (results := pair) rfl rfl
          (.cons (Evaluates.lookup (by simp [ScalarEnv.set]))
            (.cons (Evaluates.lookup (by simp [ScalarEnv.set])) .nil))
        simpa only [loopContinuation, show loopControl iteration = false from rfl,
          Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one] using rest
      · rw [scan_succ, if_neg better]
        have rest := ih (first + 1) bestD bestX (by omega) ready
          (by simpa [ready, entered, ScalarEnv.set] using getBestD)
          (by simpa [ready, entered, ScalarEnv.set] using getBestX)
        apply BlockReturns.range_step (by simp [rangeContinues]; omega)
        apply BlockReturns.assign (value := natural (minimum first))
          (Evaluates.call (.cons (Evaluates.lookup (by simp [ScalarEnv.set])) .nil) (minimal_x.result first))
        apply BlockReturns.branch (value := .bool false) (by simpa only [better, decide_false] using tested)
        simpa only [loopContinuation, show loopControl iteration = false from rfl,
          Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one] using rest

theorem result (limit : Int) : ReturnsValue program "naive" [number limit] (natural (answer limit)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := natural 0) Evaluates.constant
  apply BlockReturns.assign (value := natural 0) Evaluates.constant
  apply BlockReturns.for_range (values := [natural 2, number (limit + 1)])
    (.cons Evaluates.constant (.cons (Evaluates.binary (av := number limit) (bv := number 1)
      (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary, number])) .nil)) rfl
  exact loop_result (limit + 1) 2 (limit - 1).toNat 0 0 (by omega) _ rfl rfl

end data.«project-euler-statements».data.py.project_euler_statements.p66.naive
