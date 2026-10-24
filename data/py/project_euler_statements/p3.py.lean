import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p3.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerStatements.P3
import Mathlib.Tactic

namespace data.«project-euler-statements».data.py.project_euler_statements.p3
open FormalSW.PyAst FormalSW.PyAst.Calls
open ProjectEulerStatements.P3

private def factorTest : Expr :=
  .boolOp .and
    [.compare (.binOp (.name "n") .mod (.name "k")) [(.eq, .constant (.int 0))],
     .call (.name "is_prime") [.name "k"]]

private def scanBody : List Stmt :=
  [.ifThen factorTest [.return (.name "k")] []]

private theorem factor_test (program : Module)
    (prime : ∀ k : Nat, ReturnsValue program "is_prime" [.int k] (.bool (decide (Nat.Prime k))))
    (n k : Nat) (hk : 2 ≤ k) (env : ScalarEnv)
    (hn : env "n" = some (.int n)) (he : env "k" = some (.int k)) :
    Evaluates program env factorTest (.bool (decide (isPrimeFactor n k))) := by
  have divides : Evaluates program env
      (.compare (.binOp (.name "n") .mod (.name "k")) [(.eq, .constant (.int 0))])
      (.bool (decide (k ∣ n))) := by
    apply Evaluates.compare (av := .int ↑(n % k)) (bv := .int 0)
    · exact Evaluates.binary (Evaluates.lookup hn) (Evaluates.lookup he)
        (by simp [scalarBinary, show k ≠ 0 by omega])
    · exact Evaluates.constant
    · simp [scalarCompare, evalCmpOp, Int.natCast_dvd_natCast]
  by_cases hdvd : k ∣ n
  · apply Evaluates.boolean_continue (first := .bool true)
    · simpa [hdvd] using divides
    · rfl
    · apply Evaluates.boolean_last
      simpa [isPrimeFactor, hk, hdvd] using
        Evaluates.call (.cons (Evaluates.lookup he) .nil) (prime k)
  · simp only [isPrimeFactor, hdvd, false_and, and_false, decide_false]
    apply Evaluates.boolean_stop (value := .bool false)
    · simpa [hdvd] using divides
    · rfl

private theorem scan_result (program : Module)
    (prime : ∀ k : Nat, ReturnsValue program "is_prime" [.int k] (.bool (decide (Nat.Prime k))))
    (n k : Nat) (env : ScalarEnv) (hn : env "n" = some (.int n)) :
    BlockReturns program env
      [.rangeStepLoop "k" k 1 (-1) scanBody [], .return (.constant (.int 0))]
      (.int (Nat.findGreatest (isPrimeFactor n) k)) := by
  induction k generalizing env with
  | zero =>
      apply BlockReturns.range_done (by decide)
      exact BlockReturns.return_value Evaluates.constant
  | succ k ih =>
      by_cases hk : 2 ≤ k + 1
      · apply BlockReturns.range_step (by simp [rangeContinues]; omega)
        by_cases factor : isPrimeFactor n (k + 1)
        · rw [Nat.findGreatest_eq factor]
          apply BlockReturns.branch (value := .bool true)
          · simpa [factor] using factor_test program prime n (k + 1) hk
              (env.set "k" (.int ↑(k + 1))) (by simp [ScalarEnv.set, hn])
              (by simp [ScalarEnv.set])
          · exact BlockReturns.return_value (Evaluates.lookup (by simp [ScalarEnv.set]))
        · rw [Nat.findGreatest_of_not factor]
          apply BlockReturns.branch (value := .bool false)
          · simpa [factor] using factor_test program prime n (k + 1) hk
              (env.set "k" (.int ↑(k + 1))) (by simp [ScalarEnv.set, hn])
              (by simp [ScalarEnv.set])
          · simpa using ih (env.set "k" (.int ↑(k + 1))) (by simp [ScalarEnv.set, hn])
      · have he : k = 0 := by omega
        subst k
        have absent : ¬isPrimeFactor n 1 := by simp [isPrimeFactor]
        rw [Nat.findGreatest_of_not absent]
        apply BlockReturns.range_done (by decide)
        exact BlockReturns.return_value Evaluates.constant

/-- The source scan computes the mathematical reference whenever its imported
primality helper is linked with its proved meaning. -/
theorem naive.result_in (program : Module)
    (declaration : findFunctionIn program.body "naive" = findFunctionIn P3Ast.module.body "naive")
    (prime : ∀ k : Nat, ReturnsValue program "is_prime" [.int k] (.bool (decide (Nat.Prime k))))
    (n : Nat) :
    ReturnsValue program "naive" [.int n] (.int (Nat.findGreatest (isPrimeFactor n) n)) := by
  apply BlockReturns.function (declaration.trans rfl) rfl
  apply BlockReturns.for_range (values := [.int n, .int 1, .int (-1)])
  · exact .cons (Evaluates.lookup rfl) (.cons Evaluates.constant
      (.cons (Evaluates.unary Evaluates.constant rfl) .nil))
  · rfl
  · exact scan_result program prime n n _ rfl

private theorem common_extension : Extends P3Ast.module CommonAst.module := by
  change Extends { body := P3Ast.module.body.take 2 ++ CommonAst.module.body } CommonAst.module
  apply Extends.prepend
  · intro name member
    change name ∈ ["naive"] at member
    have only : name = "naive" := by simpa using member
    subst name
    decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

theorem naive.result (n : Nat) :
    ReturnsValue P3Ast.module "naive" [.int n] (.int (Nat.findGreatest (isPrimeFactor n) n)) := by
  apply naive.result_in P3Ast.module rfl
  intro k
  exact (common.is_prime.result k).extend common_extension

theorem naive.«Returns» (n : Int) (hp : Calls.Condition P3Ast.module
      (fun key => if key = "n" then some (.int n) else none) P3Ast.requires_naive_0) :
    (Calls.function P3Ast.module "naive" [.int n]).Returns := by
  have hn : n ≥ 2 := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  simpa [Int.toNat_of_nonneg (by omega : 0 ≤ n)] using (naive.result n.toNat).returns

end data.«project-euler-statements».data.py.project_euler_statements.p3
