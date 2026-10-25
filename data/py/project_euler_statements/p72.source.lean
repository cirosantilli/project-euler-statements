import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p72.py.ast»
import lang.py.FormalSW.Calls
import ProjectEulerStatements.P72

/-! Source generator sums count all coprime residues, then all allowed denominators. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p72
open FormalSW.PyAst Calls ProjectEulerStatements.ReducedFractionCount
set_option Elab.async false

abbrev program := P72Ast.module
abbrev number (n : Nat) : Constant := .int n
abbrev gcdCondition : Expr := .compare (.call (.name "gcd") [.name "n", .name "d"])
  [(.eq, .constant (.int 1))]
abbrev countCondition : Expr := .boolOp .and
  [.compare (.name "n") [(.lt, .name "d")], gcdCondition]

def remainingCount (d first : Nat) : Nat :=
  ((Finset.Ico first d).filter (fun n => Nat.gcd n d = 1)).card

theorem count_done (d first : Nat) (finished : d ≤ first) : remainingCount d first = 0 := by
  simp [remainingCount, Finset.Ico_eq_empty_of_le finished]

theorem count_step (d first : Nat) (active : first < d) :
    remainingCount d first =
      (if Nat.gcd first d = 1 then 1 else 0) + remainingCount d (first + 1) := by
  have interval : Finset.Ico first d = insert first (Finset.Ico (first + 1) d) := by
    ext n
    simp only [Finset.mem_insert, Finset.mem_Ico]
    omega
  unfold remainingCount
  rw [interval]
  by_cases chosen : Nat.gcd first d = 1
  · simp [Finset.filter_insert, chosen, Finset.mem_filter, Finset.mem_Ico, Nat.add_comm]
  · simp [Finset.filter_insert, chosen]

theorem count_condition_result (d n : Nat) (env : ScalarEnv)
    (getD : env "d" = some (number d)) (getN : env "n" = some (number n))
    (active : n < d) :
    Evaluates program env (.boolOp .and [countCondition])
      (.bool (decide (Nat.gcd n d = 1))) := by
  apply Evaluates.boolean_last
  apply Evaluates.boolean_continue (first := .bool true)
  · apply Evaluates.compare (Evaluates.lookup getN) (Evaluates.lookup getD)
    simp [scalarCompare, evalCmpOp, active]
  · rfl
  · apply Evaluates.boolean_last
    apply Evaluates.compare (av := number (Nat.gcd n d)) (bv := number 1)
    · apply Evaluates.library_call
        (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getD) .nil)) rfl
      change some (Math.gcdCall [.int n, .int d]) = _
      simpa using congrArg some (Math.gcdCall_pair (n : Int) (d : Int))
    · exact Evaluates.constant
    · simp [scalarCompare, evalCmpOp]

theorem count_loop (d first total : Nat) (env : ScalarEnv)
    (getD : env "d" = some (number d)) :
    SumReturns program ⟨"n", .constant (.int 1), [countCondition], d, 1, env⟩
      first total (total + remainingCount d first) := by
  by_cases active : first < d
  · have tested := count_condition_result d first (env.set "n" (number first))
      (by simpa [ScalarEnv.set] using getD) (by simp [ScalarEnv.set]) active
    by_cases chosen : Nat.gcd first d = 1
    · apply SumReturns.keep (by simp [rangeContinues]; omega)
        (by simpa only [chosen, decide_true] using tested) rfl (item := number 1)
        (updated := (total : Int) + 1) Evaluates.constant rfl
      have continued := count_loop d (first + 1) (total + 1) env getD
      simpa only [count_step d first active, chosen, if_true, Nat.cast_add,
        Nat.cast_one, Int.add_assoc] using continued
    · apply SumReturns.skip (by simp [rangeContinues]; omega)
        (by simpa only [chosen, decide_false] using tested) rfl
      have continued := count_loop d (first + 1) total env getD
      simpa only [count_step d first active, chosen, if_false, Nat.zero_add,
        Nat.cast_add, Nat.cast_one] using continued
  · have empty := count_done d first (by omega)
    simpa only [empty, Nat.add_zero] using
      (SumReturns.done (module := program)
        (sum := ⟨"n", .constant (.int 1), [countCondition], d, 1, env⟩)
        (next := first) (total := total) (by simp [rangeContinues]; omega))
termination_by d - first
decreasing_by all_goals omega

theorem count_reduced.natural_result (d : Nat) :
    ReturnsValue program "count_reduced" [number d] (number d.totient) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range (.cons (Evaluates.lookup rfl) .nil) rfl
  have count : remainingCount d 0 = d.totient := by
    simpa [remainingCount, countReduced, Nat.Ico_zero_eq_range] using countReduced_eq_totient d
  simpa only [count, Nat.cast_zero, Int.zero_add] using
    count_loop d 0 0 (argumentEnv [⟨"d", some (.name "int"), none⟩] [number d]) rfl

theorem count_reduced.result (d : Int) :
    ReturnsValue program "count_reduced" [.int d] (number d.toNat.totient) := by
  by_cases negative : d < 0
  · have clipped : d.toNat = 0 := by omega
    rw [clipped, Nat.totient_zero]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.sum_range (.cons (Evaluates.lookup rfl) .nil) rfl
    exact SumReturns.done (by simp [rangeContinues]; omega)
  · have cast : (d.toNat : Int) = d := Int.toNat_of_nonneg (by omega)
    simpa only [number, cast] using count_reduced.natural_result d.toNat

abbrev denominatorCondition : Expr := .compare (.name "d") [(.gt, .constant (.int 1))]
abbrev countExpression : Expr := .call (.name "count_reduced") [.name "d"]

/-- The outer generator includes precisely denominators greater than one. -/
theorem total_loop (stop : Int) (first count total : Nat) (env : ScalarEnv)
    (length : (stop - first).toNat = count) :
    SumReturns program ⟨"d", countExpression, [denominatorCondition], stop, 1, env⟩
      first total (total + ((List.range' first count).map contribution).sum) := by
  induction count generalizing first total with
  | zero =>
      apply SumReturns.done
      simp [rangeContinues]
      omega
  | succ count ih =>
      have tested : Evaluates program (env.set "d" (number first))
          (.boolOp .and [denominatorCondition]) (.bool (decide (1 < first))) := by
        apply Evaluates.boolean_last
        apply Evaluates.compare (av := number first) (bv := number 1)
          (Evaluates.lookup (by simp [ScalarEnv.set])) Evaluates.constant
        simp [scalarCompare, evalCmpOp]
      by_cases chosen : 1 < first
      · apply SumReturns.keep (by simp [rangeContinues]; omega)
          (by simpa only [chosen, decide_true] using tested) rfl
          (item := number first.totient) (updated := (total : Int) + first.totient)
          (Evaluates.call (.cons (Evaluates.lookup (by rfl)) .nil)
            (count_reduced.natural_result first)) rfl
        simpa only [List.range'_succ, List.map_cons, List.sum_cons, contribution,
          if_pos chosen, Nat.cast_add, Nat.cast_one, Int.add_assoc] using
          ih (first + 1) (total + first.totient) (by omega)
      · apply SumReturns.skip (by simp [rangeContinues]; omega)
          (by simpa only [chosen, decide_false] using tested) rfl
        simpa only [List.range'_succ, List.map_cons, List.sum_cons, contribution,
          if_neg chosen, Nat.zero_add, Nat.cast_add, Nat.cast_one] using
          ih (first + 1) total (by omega)

theorem naive.result (limit : Int) :
    ReturnsValue program "naive" [.int limit]
      (number (ProjectEulerStatements.ReducedFractionCount.result limit)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range (values := [.int (limit + 1)])
    (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil) rfl
  simpa only [ProjectEulerStatements.ReducedFractionCount.result, List.range_eq_range',
    Nat.zero_add, Nat.cast_zero, Int.zero_add, Int.sub_zero] using
    total_loop (limit + 1) 0 (limit + 1).toNat 0
      (argumentEnv [⟨"limit", some (.name "int"), none⟩] [.int limit]) (by omega)

end data.«project-euler-statements».data.py.project_euler_statements.p72
