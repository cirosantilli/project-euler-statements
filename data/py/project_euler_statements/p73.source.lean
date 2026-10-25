import data.«project-euler-statements».data.py.project_euler_statements.«p73.conditions.source»

/-! The exhaustive Python row and denominator generators implement finite interval counts. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p73
open FormalSW.PyAst Calls ProjectEulerStatements.FractionIntervalCount
set_option Elab.async false

namespace count_between

theorem loop_result (p : Bounds) (d first : Int) (total : Nat) (env : ScalarEnv)
    (captured : Captured p env) (getD : env "d" = some (number d)) :
    SumReturns program ⟨"n", .constant (.int 1), [countCondition], d, 1, env⟩
      first total (total + count (accepted p d) first d : Nat) := by
  by_cases active : first < d
  · have entered := captured.set "n" (number first)
      (by decide) (by decide) (by decide) (by decide)
    have tested := condition_result p d first (env.set "n" (number first)) entered
      (by simpa [ScalarEnv.set] using getD) (by simp [ScalarEnv.set])
    by_cases chosen : accepted p d first
    · apply SumReturns.keep (by simp [rangeContinues]; omega)
        (by simpa only [chosen, decide_true] using tested) rfl
        (item := .int 1) (updated := (total : Int) + 1) Evaluates.constant rfl
      have continued := loop_result p d (first + 1) (total + 1) env captured getD
      simpa only [count_step _ first d active, chosen, if_true, Nat.cast_add,
        Nat.cast_one, Int.add_assoc] using continued
    · apply SumReturns.skip (by simp [rangeContinues]; omega)
        (by simpa only [chosen, decide_false] using tested) rfl
      have continued := loop_result p d (first + 1) total env captured getD
      simpa only [count_step _ first d active, chosen, if_false, Nat.zero_add,
        Nat.cast_add, Nat.cast_one] using continued
  · have empty := count_empty (accepted p d) first d (by omega)
    simpa only [empty, Nat.add_zero] using
      (SumReturns.done (module := program)
        (sum := ⟨"n", .constant (.int 1), [countCondition], d, 1, env⟩)
        (next := first) (total := total) (by simp [rangeContinues]; omega))
termination_by (d - first).toNat
decreasing_by all_goals omega

theorem result (d : Int) (p : Bounds) :
    ReturnsValue program "count_between" (values d p) (number (row p d)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range (.cons Evaluates.constant (.cons (Evaluates.lookup rfl) .nil)) rfl
  simpa only [row, Nat.zero_add, Nat.cast_zero, Int.zero_add] using
    loop_result p d 1 0 (argumentEnv helperArgs (values d p)) ⟨rfl, rfl, rfl, rfl⟩ rfl

end count_between

abbrev countExpression : Expr := .call (.name "count_between")
  [.name "d", .name "lower_num", .name "lower_den", .name "upper_num", .name "upper_den"]

/-- Every denominator contributes one complete exhaustive numerator count. -/
theorem total_loop (p : Bounds) (stop first : Int) (count total : Nat) (env : ScalarEnv)
    (captured : Captured p env) (length : (stop - first).toNat = count) :
    SumReturns program ⟨"d", countExpression, [], stop, 1, env⟩
      first total (total + rows p first count : Nat) := by
  induction count generalizing first total with
  | zero =>
      apply SumReturns.done
      simp [rangeContinues]
      omega
  | succ count ih =>
      have entered := captured.set "d" (number first)
        (by decide) (by decide) (by decide) (by decide)
      apply SumReturns.keep (by simp [rangeContinues]; omega) Evaluates.constant rfl
        (item := number (row p first)) (updated := (total : Int) + row p first)
      · apply Evaluates.call
          (.cons (Evaluates.lookup (by simp [ScalarEnv.set]))
            (.cons (Evaluates.lookup entered.lowerNum) (.cons (Evaluates.lookup entered.lowerDen)
              (.cons (Evaluates.lookup entered.upperNum)
                (.cons (Evaluates.lookup entered.upperDen) .nil)))))
          (count_between.result first p)
      · rfl
      · simpa only [rows, Nat.cast_add, Nat.cast_one, Int.add_assoc] using
          ih (first + 1) (total + row p first) (by omega)

namespace naive

theorem body_result (limit : Int) (p : Bounds) :
    BlockReturns program (argumentEnv naiveArgs (values limit p))
      (executableBody ((findFunctionIn program.body "naive").getD ([], [])).2)
      (number (ProjectEulerStatements.FractionIntervalCount.result p limit)) := by
  apply BlockReturns.return_value
  apply Evaluates.sum_range (values := [.int 2, .int (limit + 1)])
    (.cons Evaluates.constant (.cons (Evaluates.binary (Evaluates.lookup rfl)
      Evaluates.constant rfl) .nil)) rfl
  simpa only [ProjectEulerStatements.FractionIntervalCount.result, Nat.zero_add,
    Nat.cast_zero, Int.zero_add] using
    total_loop p (limit + 1) 2 (limit - 1).toNat 0 (argumentEnv naiveArgs (values limit p))
      ⟨rfl, rfl, rfl, rfl⟩ (by omega)

theorem result (limit : Int) (p : Bounds) :
    ReturnsValue program "naive" (values limit p)
      (number (ProjectEulerStatements.FractionIntervalCount.result p limit)) :=
  BlockReturns.function rfl rfl (body_result limit p)

/-- Every omitted trailing-default call reuses the same complete symbolic execution proof. -/
theorem default_result (limit : Int) (p : Bounds) (supplied : List Constant)
    (omitted : naiveArgs.length ≠ supplied.length)
    (completed : completeArguments naiveArgs supplied = some (values limit p)) :
    ReturnsValue program "naive" supplied
      (number (ProjectEulerStatements.FractionIntervalCount.result p limit)) :=
  ReturnsValue.with_defaults rfl omitted completed rfl (result limit p)

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p73
