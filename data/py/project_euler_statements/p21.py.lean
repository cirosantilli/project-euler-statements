import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p21.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerStatements.P21
import Mathlib.Data.List.Range

namespace data.«project-euler-statements».data.py.project_euler_statements.p21
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := P21Ast.module

private def selectedSum (test : Nat → Bool) (start count : Nat) : Nat :=
  ((List.range' start count).filter test).sum

/-- A filtered finite range sums the selected indices, evaluating each predicate. -/
private theorem filtered_sum (count start total : Nat) (env : ScalarEnv) (name : String)
    (conditions : List Expr) (test : Nat → Bool)
    (tested : ∀ n, start ≤ n → n < start + count →
      Evaluates program (env.set name (.int n))
        (if conditions.isEmpty then .constant (.bool true) else .boolOp .and conditions) (.bool (test n))) :
    SumReturns program ⟨name, .name name, conditions, start + count, 1, env⟩ start total
      (total + selectedSum test start count) := by
  induction count generalizing start total with
  | zero =>
      simpa [selectedSum] using SumReturns.done (module := program)
        (sum := ⟨name, .name name, conditions, start, 1, env⟩) (next := start) (total := total)
        (by simp [rangeContinues])
  | succ count ih =>
      have evaluated := tested start (by omega) (by omega)
      have tailTest : ∀ n, start + 1 ≤ n → n < start + 1 + count →
          Evaluates program (env.set name (.int n))
            (if conditions.isEmpty then .constant (.bool true) else .boolOp .and conditions) (.bool (test n)) := by
        intro n lower upper
        exact tested n (by omega) (by omega)
      cases chosen : test start with
      | false =>
          simp only [chosen] at evaluated
          apply SumReturns.skip (by simp [rangeContinues]) evaluated rfl
          simpa [selectedSum, List.range'_succ, chosen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm] using ih (start + 1) total tailTest
      | true =>
          simp only [chosen] at evaluated
          apply SumReturns.keep (by simp [rangeContinues]) evaluated rfl (item := .int start)
            (updated := total + start)
          · exact Evaluates.lookup (by simp [ScalarEnv.set])
          · rfl
          · simpa [selectedSum, List.range'_succ, chosen, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm] using ih (start + 1) (total + start) tailTest

private def properSum (n : Nat) : Nat := selectedSum (fun d => decide (n % d = 0)) 1 (n - 1)

private theorem divisor_sum_result (n : Nat) :
    ReturnsValue program "proper_divisor_sum" [.int n] (.int (properSum n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (c := .int n) (Evaluates.lookup rfl)
  by_cases zero : n = 0
  · subst n
    exact Evaluates.constant
  · simp only [scalarTruth, bne_iff_ne, ne_eq, Int.natCast_eq_zero, zero, not_false_eq_true, ↓reduceIte]
    apply Evaluates.sum_range (.cons Evaluates.constant (.cons (Evaluates.lookup rfl) .nil)) rfl
    have sum := filtered_sum (n - 1) 1 0 (argumentEnv [⟨"n", some (.name "int"), none⟩] [.int n]) "d"
      [.compare (.binOp (.name "n") .mod (.name "d")) [(.eq, .constant (.int 0))]]
      (fun d => decide (n % d = 0)) (by
        intro d lower upper
        apply Evaluates.boolean_last
        apply Evaluates.compare (av := .int ↑(n % d)) (bv := .int 0)
        · apply Evaluates.binary (av := .int n) (bv := .int d) (Evaluates.lookup (by simp [ScalarEnv.set, argumentEnv]))
            (Evaluates.lookup (by simp [ScalarEnv.set]))
          simp [scalarBinary, show d ≠ 0 by omega, show 0 < d by omega]
        · exact Evaluates.constant
        · simp [scalarCompare, evalCmpOp, ← Int.dvd_iff_emod_eq_zero, Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero])
    have count : (1 : Int) + (n - 1 : Nat) = n := by omega
    simpa only [count, Nat.cast_one, Nat.cast_zero, Int.zero_add, properSum] using sum

private theorem d_result (n : Nat) : ReturnsValue program "d" [.int n] (.int (properSum n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (divisor_sum_result n)

private def amicable (n : Nat) : Bool := decide (properSum n ≠ n ∧ properSum (properSum n) = n)

private theorem amicable_result (n : Nat) : ReturnsValue program "is_amicable" [.int n] (.bool (amicable n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (d_result n))
  apply BlockReturns.return_value
  have test : Evaluates program
      ((argumentEnv [⟨"n", some (.name "int"), none⟩] [.int n]).set "m" (.int (properSum n)))
      (.compare (.name "m") [(.notEq, .name "n")]) (.bool (decide (properSum n ≠ n))) := by
    apply Evaluates.compare (Evaluates.lookup rfl) (Evaluates.lookup rfl)
    simp [scalarCompare, evalCmpOp]
  by_cases different : properSum n ≠ n
  · apply Evaluates.boolean_continue test (by simp [scalarTruth, different])
    apply Evaluates.boolean_last
    apply Evaluates.compare
      (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (d_result (properSum n))) (Evaluates.lookup rfl)
    simp [scalarCompare, evalCmpOp, amicable, different]
  · have same : amicable n = false := by simp [amicable, different]
    rw [same]
    exact Evaluates.boolean_stop (by simpa [different] using test) rfl

theorem naive.empty_result (limit : Int) (small : limit ≤ 1) :
    ReturnsValue program "naive" [.int limit] (.int 0) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range (.cons Evaluates.constant (.cons (Evaluates.lookup rfl) .nil)) rfl
  exact SumReturns.done (by simp [rangeContinues]; omega)

private theorem naive.sum_result (limit : Nat) :
    ReturnsValue program "naive" [.int limit] (.int (selectedSum amicable 1 (limit - 1))) := by
  by_cases zero : limit = 0
  · subst limit
    exact naive.empty_result 0 (by omega)
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.sum_range (.cons Evaluates.constant (.cons (Evaluates.lookup rfl) .nil)) rfl
    have summed := filtered_sum (limit - 1) 1 0
      (argumentEnv [⟨"limit", some (.name "int"), none⟩] [.int limit]) "n"
      [.call (.name "is_amicable") [.name "n"]] amicable (by
        intro n _ _
        exact Evaluates.boolean_last (Evaluates.call
          (.cons (Evaluates.lookup (by simp [ScalarEnv.set])) .nil) (amicable_result n)))
    have count : (1 : Int) + (limit - 1 : Nat) = limit := by omega
    simpa only [count, Nat.cast_one, Nat.cast_zero, Int.zero_add] using summed

theorem naive.«Returns» (limit : Int) :
    (Calls.function program "naive" [.int limit]).Returns := by
  by_cases small : limit ≤ 1
  · exact (naive.empty_result limit small).returns
  · lift limit to Nat using (by omega : 0 ≤ limit)
    exact (naive.sum_result limit).returns

private theorem selectedSum_interval (test : Nat → Bool) (n : Nat) :
    selectedSum test 1 (n - 1) =
      ((Finset.Icc 1 (n - 1)).filter (fun d => test d = true)).sum (fun d => d) := by
  have same : ((List.range' 1 (n - 1)).filter test).toFinset =
      (Finset.Icc 1 (n - 1)).filter (fun d => test d = true) := by
    ext d
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range', Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨k, lower, rfl⟩, accepted⟩
      exact ⟨⟨by omega, by omega⟩, accepted⟩
    · rintro ⟨⟨lower, upper⟩, accepted⟩
      exact ⟨⟨d - 1, by omega, by omega⟩, accepted⟩
  rw [← same, List.sum_toFinset]
  · simp [selectedSum]
  · exact (List.nodup_range' (s := 1) (n := n - 1)).filter _

private theorem properSum_eq (n : Nat) : properSum n = ProjectEulerStatements.P21.d n := by
  simp [properSum, selectedSum_interval, ProjectEulerStatements.P21.d,
    ProjectEulerStatements.P21.properDivisors, Nat.dvd_iff_mod_eq_zero]

/-- The source returns the finite sum in the mathematical statement. -/
theorem naive.result (limit : Nat) : ReturnsValue program "naive" [.int limit]
    (.int (ProjectEulerStatements.P21.naive limit)) := by
  have same : selectedSum amicable 1 (limit - 1) = ProjectEulerStatements.P21.naive limit := by
    simp [selectedSum_interval, amicable, properSum_eq, ProjectEulerStatements.P21.naive,
      ProjectEulerStatements.P21.isAmicable]
  simpa only [same] using naive.sum_result limit

end data.«project-euler-statements».data.py.project_euler_statements.p21
