import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p6.py.ast»
import FormalSW
import ProjectEulerStatements.P6
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace data.«project-euler-statements».data.py.project_euler_statements.p6
open FormalSW.PyAst FormalSW.PyAst.Calls
open scoped BigOperators
private abbrev program := P6Ast.module

private theorem interval_sum_step (f : Nat → Nat) (x n : Nat) (active : x ≤ n) :
    (∑ i ∈ Finset.Icc x n, f i) = f x + ∑ i ∈ Finset.Icc (x + 1) n, f i := by
  have interval : Finset.Ioc x n = Finset.Icc (x + 1) n := by
    ext y
    simp
  rw [Finset.Icc_eq_cons_Ioc active, Finset.sum_cons, interval]

/-- The loop invariant relates the running Python integer to the remaining sum. -/
private theorem sum_result (name : String) (element : Expr) (f : Nat → Nat)
    (env : ScalarEnv) (evaluate : ∀ k : Nat,
      Evaluates program (env.set name (.int k)) element (.int (f k)))
    (n x : Nat) (total : Int) :
    SumReturns program ⟨name, element, [], n + 1, 1, env⟩ x total
      (total + ((∑ i ∈ Finset.Icc x n, f i : Nat) : Int)) := by
  induction measure : n + 1 - x using Nat.strong_induction_on generalizing x total with
  | h size ih =>
      by_cases active : x ≤ n
      · rw [interval_sum_step f x n active, Nat.cast_add]
        apply SumReturns.keep (value := .bool true) (item := .int (f x))
          (updated := total + f x)
        · simp [rangeContinues]; omega
        · exact Evaluates.constant
        · rfl
        · exact evaluate x
        · rfl
        · simpa [Int.natCast_add, Int.add_assoc] using
            ih (n + 1 - (x + 1)) (by omega) (x + 1) (total + f x) rfl
      · have empty : Finset.Icc x n = ∅ := Finset.Icc_eq_empty (by omega)
        simp only [empty, Finset.sum_empty, Nat.cast_zero, Int.add_zero]
        exact SumReturns.done (by simp [rangeContinues]; omega)

private theorem range_evaluates (name : String) (element : Expr) (f : Nat → Nat)
    (n : Nat) (env : ScalarEnv) (getN : env "n" = some (.int n))
    (evaluate : ∀ k : Nat, Evaluates program (env.set name (.int k)) element (.int (f k))) :
    Evaluates program env
      (.sumRange name element [.constant (.int 1), .binOp (.name "n") .add (.constant (.int 1))] [])
      (.int ((∑ i ∈ Finset.Icc 1 n, f i : Nat) : Int)) := by
  apply Evaluates.sum_range (values := [.int 1, .int ((n + 1 : Nat) : Int)])
  · exact .cons Evaluates.constant (.cons
      (Evaluates.binary (Evaluates.lookup getN) Evaluates.constant (by simp [scalarBinary])) .nil)
  · rfl
  · simpa using sum_result name element f env evaluate n 1 0

private theorem sum_squares_result (n : Nat) :
    ReturnsValue program "sum_squares" [.int n] (.int (ProjectEulerStatements.P6.sumSquares n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply range_evaluates "i" (.binOp (.name "i") .mult (.name "i")) (fun i => i ^ 2) n _ rfl
  intro k
  exact Evaluates.binary (av := .int k) (bv := .int k) (Evaluates.lookup (by simp [ScalarEnv.set]))
    (Evaluates.lookup (by simp [ScalarEnv.set])) (by simp [scalarBinary, pow_two])

private theorem square_sum_result (n : Nat) :
    ReturnsValue program "square_sum" [.int n] (.int (ProjectEulerStatements.P6.squareSum n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := .int ((∑ i ∈ Finset.Icc 1 n, i : Nat) : Int)) (bv := .int 2)
  · exact range_evaluates "" (.name "") id n _ rfl
      (fun _ => Evaluates.lookup (by simp [ScalarEnv.set]))
  · exact Evaluates.constant
  · simp [scalarBinary, ProjectEulerStatements.P6.squareSum]

/-- Natural subtraction agrees with Python subtraction on this domain. -/
theorem sum_squares_le (n : Nat) :
    ProjectEulerStatements.P6.sumSquares n ≤ ProjectEulerStatements.P6.squareSum n :=
  Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => Nat.zero_le _)

theorem naive.result (n : Nat) :
    ReturnsValue program "naive" [.int n] (.int (ProjectEulerStatements.P6.naive n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := .int (ProjectEulerStatements.P6.squareSum n))
    (bv := .int (ProjectEulerStatements.P6.sumSquares n))
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (square_sum_result n)
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (sum_squares_result n)
  · simp [scalarBinary, ProjectEulerStatements.P6.naive, Int.natCast_sub (sum_squares_le n)]

theorem naive.«Returns» (n : Int) (hp : Condition program
    (fun key => if key = "n" then some (.int n) else none) P6Ast.requires_naive_0) :
    (function program "naive" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  simpa [Int.toNat_of_nonneg nonnegative] using (naive.result n.toNat).returns

theorem naive.«Supported» (n : Int) (hp : Condition program
    (fun key => if key = "n" then some (.int n) else none) P6Ast.requires_naive_0) :
    (function program "naive" [.int n]).Supported := (naive.«Returns» n hp).supported

end data.«project-euler-statements».data.py.project_euler_statements.p6
