import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p7.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerStatements.P7
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace data.«project-euler-statements».data.py.project_euler_statements.p7
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := P7Ast.module

private theorem common_extension : Extends program CommonAst.module := by
  change Extends ⟨program.body.take 2 ++ CommonAst.module.body⟩ CommonAst.module
  apply Extends.prepend
  · intro name member
    change name ∈ ["naive"] at member
    have only : name = "naive" := by simpa using member
    subst name
    decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem prime_result (n : Nat) :
    ReturnsValue program "is_prime" [.int n] (.bool (decide (Nat.Prime n))) :=
  (common.is_prime.result n).extend common_extension

private def body : List Stmt :=
  match executableBody ((findFunctionIn program.body "naive").getD ([], [])).2 with
  | [_, _, _, .whileDo _ body _, _] => body
  | _ => []

private def condition : Expr := .compare (.name "count") [(.lt, .name "n")]

/-- Each iteration advances toward the nth prime and maintains the exact count
of primes at or below x. Infinitude supplies a finite target for every input. -/
private theorem loop_result (k x : Nat) (bound : x ≤ Nat.nth Nat.Prime k) (env : ScalarEnv)
    (getN : env "n" = some (.int (k + 1)))
    (getCount : env "count" = some (.int (Nat.count Nat.Prime (x + 1))))
    (getX : env "x" = some (.int x)) :
    BlockReturns program env [.whileDo condition body [], .return (.name "x")]
      (.int (Nat.nth Nat.Prime k)) := by
  induction measure : Nat.nth Nat.Prime k - x using Nat.strong_induction_on generalizing x env with
  | h size ih =>
      by_cases finished : x = Nat.nth Nat.Prime k
      · subst x
        apply BlockReturns.while_loop (value := .bool false)
        · apply Evaluates.compare (Evaluates.lookup getCount) (Evaluates.lookup getN)
          simp [scalarCompare, evalCmpOp, Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime]
        · exact BlockReturns.return_value (Evaluates.lookup getX)
      · have before : x < Nat.nth Nat.Prime k := by omega
        have count_bound : Nat.count Nat.Prime (x + 1) ≤ k :=
          (Nat.count_le_iff_le_nth Nat.infinite_setOf_prime).mpr
            (by change x + 1 ≤ Nat.nth Nat.Prime k; omega)
        apply BlockReturns.while_loop (value := .bool true)
        · apply Evaluates.compare (Evaluates.lookup getCount) (Evaluates.lookup getN)
          simp [scalarCompare, evalCmpOp]; omega
        · apply BlockReturns.augAssign (value := .int ((x + 1 : Nat) : Int))
          · exact Evaluates.binary (Evaluates.lookup getX) Evaluates.constant (by simp [scalarBinary])
          · have prime := Evaluates.call (module := program)
              (.cons (Evaluates.lookup (name := "x") (env := env.set "x" (.int ((x + 1 : Nat) : Int)))
                (by simp [ScalarEnv.set])) .nil) (prime_result (x + 1))
            by_cases isPrime : Nat.Prime (x + 1)
            · apply BlockReturns.branch (value := .bool true)
              · simpa [isPrime] using prime
              · apply BlockReturns.augAssign (value := .int ((Nat.count Nat.Prime (x + 1) + 1 : Nat) : Int))
                · exact Evaluates.binary (Evaluates.lookup (by simpa [ScalarEnv.set] using getCount))
                    Evaluates.constant (by simp [scalarBinary])
                · have next := ih (Nat.nth Nat.Prime k - (x + 1)) (by omega) (x + 1) (by omega)
                    ((env.set "x" (.int ((x + 1 : Nat) : Int))).set "count"
                      (.int ((Nat.count Nat.Prime (x + 1) + 1 : Nat) : Int)))
                    (by simpa [ScalarEnv.set] using getN)
                    (by simp [ScalarEnv.set, Nat.count_succ, isPrime])
                    (by simp [ScalarEnv.set]) rfl
                  simpa [body, loopContinuation] using next
            · apply BlockReturns.branch (value := .bool false)
              · simpa [isPrime] using prime
              · have next := ih (Nat.nth Nat.Prime k - (x + 1)) (by omega) (x + 1) (by omega)
                  (env.set "x" (.int ((x + 1 : Nat) : Int)))
                  (by simpa [ScalarEnv.set] using getN)
                  (by simpa [ScalarEnv.set, Nat.count_succ, isPrime] using getCount)
                  (by simp [ScalarEnv.set]) rfl
                simpa [body, loopContinuation] using next

theorem naive.result (n : Nat) :
    ReturnsValue program "naive" [.int n] (.int (ProjectEulerStatements.P7.naive n)) := by
  cases n with
  | zero =>
      apply BlockReturns.function rfl rfl
      apply BlockReturns.branch (value := .bool true)
      · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
      · exact BlockReturns.return_value Evaluates.constant
  | succ k =>
      apply BlockReturns.function rfl rfl
      apply BlockReturns.branch (value := .bool false)
      · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp]; omega)
      · apply BlockReturns.assign Evaluates.constant
        apply BlockReturns.assign Evaluates.constant
        exact loop_result k 1 (by have := (Nat.prime_nth_prime k).two_le; omega) _ rfl
          (by simp [ScalarEnv.set, Nat.count_succ]) rfl

theorem naive.«Returns» (n : Int) (hp : Condition program
    (fun key => if key = "n" then some (.int n) else none) P7Ast.requires_naive_0) :
    (function program "naive" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  simpa [Int.toNat_of_nonneg nonnegative] using (naive.result n.toNat).returns

end data.«project-euler-statements».data.py.project_euler_statements.p7
