import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p10.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerStatements.P10
import Mathlib.Tactic

namespace data.«project-euler-statements».data.py.project_euler_statements.p10
open FormalSW.PyAst FormalSW.PyAst.Calls
open scoped BigOperators
private abbrev program := P10Ast.module

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

private theorem naive_succ (n : Nat) :
    ProjectEulerStatements.P10.naive (n + 1) =
      ProjectEulerStatements.P10.naive n + if Nat.Prime n then n else 0 := by
  unfold ProjectEulerStatements.P10.naive
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_range_succ]

private def primeSum (n : Nat) (env : ScalarEnv) : RangeSum :=
  ⟨"p", .name "p", [.call (.name "is_prime") [.name "p"]], n, 1, env⟩

/-- The running sum plus the remaining prime sum is invariant across the generator. -/
private theorem sum_result (n x : Nat) (bounded : x ≤ n) (env : ScalarEnv) (acc : Int) :
    SumReturns program (primeSum n env) x acc
      (acc + (ProjectEulerStatements.P10.naive n : Int) - ProjectEulerStatements.P10.naive x) := by
  by_cases before : x < n
  · have test : Evaluates program (env.set "p" (.int x)) (primeSum n env).filter
        (.bool (decide (Nat.Prime x))) :=
      Evaluates.boolean_last (Evaluates.call (.cons (Evaluates.lookup (by simp [ScalarEnv.set])) .nil)
        ((common.is_prime.result x).extend common_extension))
    have running : rangeContinues (x : Int) (primeSum n env).stop (primeSum n env).stride = true := by
      simp [primeSum, rangeContinues, before]
    by_cases prime : Nat.Prime x
    · apply SumReturns.keep (value := .bool true) (item := .int x) (updated := acc + x) running
      · simpa [prime] using test
      · rfl
      · exact Evaluates.lookup (by simp [primeSum, ScalarEnv.set])
      · rfl
      · have rest := sum_result n (x + 1) (by omega) env (acc + x)
        have equation : (acc + x) + (ProjectEulerStatements.P10.naive n : Int) -
            ProjectEulerStatements.P10.naive (x + 1) =
              acc + (ProjectEulerStatements.P10.naive n : Int) - ProjectEulerStatements.P10.naive x := by
          rw [naive_succ]
          simp only [prime, if_true, Nat.cast_add]
          ring
        simpa only [primeSum, Nat.cast_add, Nat.cast_one, equation] using rest
    · apply SumReturns.skip (value := .bool false) running
      · simpa [prime] using test
      · rfl
      · simpa [primeSum, naive_succ, prime] using sum_result n (x + 1) (by omega) env acc
  · have equal : x = n := by omega
    subst x
    simpa using
      (SumReturns.done (module := program) (sum := primeSum n env) (next := n) (total := acc)
        (by simp [primeSum, rangeContinues]))
termination_by n - x
decreasing_by all_goals omega

theorem naive.result (n : Nat) :
    ReturnsValue program "naive" [.int n] (.int (ProjectEulerStatements.P10.naive n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range (values := [.int n])
  · exact .cons (Evaluates.lookup rfl) .nil
  · rfl
  · simpa [primeSum, ProjectEulerStatements.P10.naive] using sum_result n 0 (by omega) _ 0

theorem naive.«Returns» (n : Int) (domain : Condition program
    (fun name => if name = "n" then some (.int n) else none) P10Ast.requires_naive_0) :
    (Calls.function program "naive" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare domain rfl
  simpa [Int.toNat_of_nonneg nonnegative] using (naive.result n.toNat).returns

end data.«project-euler-statements».data.py.project_euler_statements.p10
