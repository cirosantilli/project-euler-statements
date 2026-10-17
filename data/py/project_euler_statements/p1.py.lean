import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p1.py.ast»
import FormalSW
import ProjectEulerStatements.P1
import Mathlib.Tactic

namespace data.«project-euler-statements».data.py.project_euler_statements.«p1»
open FormalSW.PyAst FormalSW.PyAst.Calls

private theorem divisible_test (name : String) (env : ScalarEnv) (n d : Nat) (hd : 0 < d)
    (hm : env name = some (.int n)) :
    Evaluates P1Ast.module env
      (.compare (.binOp (.name name) .mod (.constant (.int d))) [(.eq, .constant (.int 0))])
      (.bool (decide (d ∣ n))) := by
  apply Evaluates.compare (av := .int (n % d)) (bv := .int 0)
  · apply Evaluates.binary (Evaluates.lookup hm) Evaluates.constant
    simp [scalarBinary, hd.ne', hd]
  · exact Evaluates.constant
  · simp [scalarCompare, evalCmpOp, Int.natCast_dvd_natCast]

theorem naive.result (n : Nat) :
    ReturnsValue P1Ast.module "naive" [.int n]
      (.int (ProjectEulerStatements.P1.naive n)) := by
  induction n with
  | zero =>
      apply BlockReturns.function rfl rfl
      apply BlockReturns.branch (value := .bool true)
      · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
      · exact BlockReturns.return_value Evaluates.constant
  | succ n ih =>
      apply BlockReturns.function rfl rfl
      apply BlockReturns.branch (value := .bool false)
      · apply Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
        simp [scalarCompare, evalCmpOp]
        omega
      · apply BlockReturns.assign (value := .int n)
        · exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant
            (by simp [scalarBinary])
        · apply BlockReturns.assign (value := .int (ProjectEulerStatements.P1.naive n))
          · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) ih
          · apply BlockReturns.return_value
            apply Evaluates.conditional (c := .bool (decide (3 ∣ n ∨ 5 ∣ n)))
            · by_cases h3 : 3 ∣ n
              · simp only [h3, true_or, decide_true]
                apply Evaluates.boolean_stop (value := .bool true)
                · simpa [h3] using divisible_test "m" _ n 3 (by decide) rfl
                · rfl
              · apply Evaluates.boolean_continue (first := .bool false)
                · simpa [h3] using divisible_test "m" _ n 3 (by decide) rfl
                · rfl
                · apply Evaluates.boolean_last
                  simpa [h3] using divisible_test "m" _ n 5 (by decide) rfl
            · by_cases h : 3 ∣ n ∨ 5 ∣ n
              · simp only [h, decide_true, scalarTruth, ↓reduceIte]
                apply Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl)
                simp [scalarBinary, ProjectEulerStatements.P1.naive, h]
              · simp only [h, decide_false, scalarTruth, Bool.false_eq_true, ↓reduceIte]
                simp only [ProjectEulerStatements.P1.naive, if_neg h]
                exact Evaluates.lookup rfl

theorem naive.«Returns» (n : Int) (hp : Calls.Condition P1Ast.module
      (fun key => if key = "n" then some (.int n) else none) P1Ast.requires_naive_0) :
    (Calls.function P1Ast.module "naive" [.int n]).Returns := by
  have hn : n ≥ 0 := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  simpa [Int.toNat_of_nonneg hn] using (naive.result n.toNat).returns

private def filterExpr : Expr :=
  .boolOp .or
    [.compare (.binOp (.name "x") .mod (.constant (.int 3))) [(.eq, .constant (.int 0))],
     .compare (.binOp (.name "x") .mod (.constant (.int 5))) [(.eq, .constant (.int 0))]]

private theorem filter_result (env : ScalarEnv) (n : Nat)
    (hx : env "x" = some (.int n)) :
    Evaluates P1Ast.module env filterExpr (.bool (decide (3 ∣ n ∨ 5 ∣ n))) := by
  by_cases h3 : 3 ∣ n
  · simp only [h3, true_or, decide_true]
    apply Evaluates.boolean_stop (value := .bool true)
    · simpa [h3] using divisible_test "x" env n 3 (by decide) hx
    · rfl
  · apply Evaluates.boolean_continue (first := .bool false)
    · simpa [h3] using divisible_test "x" env n 3 (by decide) hx
    · rfl
    · apply Evaluates.boolean_last
      simpa [h3] using divisible_test "x" env n 5 (by decide) hx

private def generator (env : ScalarEnv) (n : Nat) : RangeSum :=
  ⟨"x", .name "x", [filterExpr], n, 1, env⟩

private theorem generator_result (env : ScalarEnv) (n i : Nat) (hi : i ≤ n) (total : Int) :
    SumReturns P1Ast.module (generator env n) i total
      (total + ProjectEulerStatements.P1.naive n - ProjectEulerStatements.P1.naive i) := by
  induction hi using Nat.decreasingInduction generalizing total with
  | self =>
      simpa using (SumReturns.done (module := P1Ast.module) (sum := generator env n)
        (next := n) (total := total) (by simp [generator, rangeContinues]))
  | of_succ i hi ih =>
      have test : Evaluates P1Ast.module ((generator env n).env.set "x" (.int i))
          (generator env n).filter (.bool (decide (3 ∣ i ∨ 5 ∣ i))) := by
        apply Evaluates.boolean_last
        exact filter_result _ i rfl
      by_cases divides : 3 ∣ i ∨ 5 ∣ i
      · apply SumReturns.keep (value := .bool true) (item := .int i) (updated := total + i)
        · simp [generator, rangeContinues, hi]
        · simpa [divides] using test
        · rfl
        · exact Evaluates.lookup rfl
        · rfl
        · convert ih (total + i) using 1
          simp [ProjectEulerStatements.P1.naive, divides]
          ring
      · apply SumReturns.skip (value := .bool false)
        · simp [generator, rangeContinues, hi]
        · simpa [divides] using test
        · rfl
        · simpa [generator, ProjectEulerStatements.P1.naive, divides,
            Int.natCast_add, Int.natCast_one] using ih total

theorem naive2.result (n : Nat) :
    ReturnsValue P1Ast.module "naive2" [.int n] (.int (ProjectEulerStatements.P1.naive2 n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range (values := [.int n])
  · exact .cons (Evaluates.lookup rfl) .nil
  · rfl
  · simpa [generator, ProjectEulerStatements.P1.naive, ProjectEulerStatements.P1.naive_eq_naive2]
      using generator_result _ n 0 (Nat.zero_le n) 0

theorem naive2.«Equiv(naive)» (n : Int) (hp : Calls.Condition P1Ast.module
      (fun key => if key = "max_" then some (.int n) else none) P1Ast.requires_naive2_0) :
    (Calls.function P1Ast.module "naive2" [.int n]).Equiv
      (Calls.function P1Ast.module "naive" [.int n]) := by
  have hn : n ≥ 0 := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  have result := naive2.result n.toNat
  rw [← ProjectEulerStatements.P1.naive_eq_naive2] at result
  simpa [Int.toNat_of_nonneg hn] using result.equiv (naive.result n.toNat)

end data.«project-euler-statements».data.py.project_euler_statements.«p1»
