import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p5.py.ast»
import FormalSW
import ProjectEulerStatements.P5

namespace data.«project-euler-statements».data.py.project_euler_statements.p5
open FormalSW.PyAst FormalSW.PyAst.Calls
private abbrev program := P5Ast.module

private def body : List Stmt :=
  match executableBody ((findFunctionIn program.body "naive").getD ([], [])).2 with
  | [_, .forIn _ _ body _, _] => body
  | _ => []

/-- The source expression computes the lcm with a positive factor, so its gcd
is nonzero and Python integer division cannot raise ZeroDivisionError. -/
private theorem update_evaluates (acc x : Nat) (positive : 0 < x) (env : ScalarEnv)
    (getAcc : env "acc" = some (.int acc)) (getX : env "x" = some (.int x)) :
    Evaluates program env
      (.binOp (.binOp (.name "acc") .mult (.name "x")) .floorDiv
        (.call (.name "gcd") [.name "acc", .name "x"]))
      (.int (Nat.lcm acc x)) := by
  apply Evaluates.binary (av := .int ((acc * x : Nat) : Int))
    (bv := .int (Nat.gcd acc x))
  · exact Evaluates.binary (Evaluates.lookup getAcc) (Evaluates.lookup getX) (by simp [scalarBinary])
  · apply Evaluates.library_call (.cons (Evaluates.lookup getAcc) (.cons (Evaluates.lookup getX) .nil)) rfl
    change some (Math.gcdCall [.int acc, .int x]) = _
    simpa using congrArg some (Math.gcdCall_pair (acc : Int) (x : Int))
  · simp [scalarBinary, positive, ne_of_gt positive, Nat.lcm]

private theorem interval_step (x n acc : Nat) (active : x ≤ n) :
    Nat.lcm acc ((Finset.Icc x n).lcm id) =
      Nat.lcm (Nat.lcm acc x) ((Finset.Icc (x + 1) n).lcm id) := by
  have interval : Finset.Ioc x n = Finset.Icc (x + 1) n := by
    ext y
    simp
  rw [Finset.Icc_eq_cons_Ioc active]
  simp [Finset.lcm_insert, interval, Nat.lcm_assoc]
  rfl

private theorem loop_result (n x acc : Nat) (positive : 0 < x) (env : ScalarEnv)
    (getAcc : env "acc" = some (.int acc)) :
    BlockReturns program env [.rangeStepLoop "x" x (n + 1) 1 body [], .return (.name "acc")]
      (.int (Nat.lcm acc ((Finset.Icc x n).lcm id))) := by
  induction measure : n + 1 - x using Nat.strong_induction_on generalizing x acc env with
  | h size ih =>
      by_cases active : x ≤ n
      · rw [interval_step x n acc active]
        apply BlockReturns.range_step (by simp [rangeContinues]; omega)
        apply BlockReturns.assign (update_evaluates acc x positive _
          (by simpa [ScalarEnv.set] using getAcc) (by simp [ScalarEnv.set]))
        have next := ih (n + 1 - (x + 1)) (by omega) (x + 1) (Nat.lcm acc x)
          (by omega) ((env.set "x" (.int x)).set "acc" (.int (Nat.lcm acc x)))
          (by simp [ScalarEnv.set]) rfl
        simpa [loopContinuation, body, Int.natCast_add] using next
      · have empty : Finset.Icc x n = ∅ := Finset.Icc_eq_empty (by omega)
        simp only [empty, Finset.lcm_empty, Nat.lcm_one_right]
        apply BlockReturns.range_done (by simp [rangeContinues]; omega)
        exact BlockReturns.return_value (Evaluates.lookup getAcc)

theorem naive.result (n : Nat) :
    ReturnsValue program "naive" [.int n] (.int (ProjectEulerStatements.P5.naive n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_range (values := [.int 1, .int ((n + 1 : Nat) : Int)])
  · exact .cons Evaluates.constant (.cons
      (Evaluates.binary (Evaluates.lookup (value := .int n) (by simp [ScalarEnv.set, argumentEnv]))
        Evaluates.constant (by simp [scalarBinary])) .nil)
  · rfl
  · simpa [ProjectEulerStatements.P5.naive] using loop_result n 1 1 (by decide) _ rfl

theorem naive.«Returns» (n : Int) (hp : Condition program
    (fun key => if key = "n" then some (.int n) else none) P5Ast.requires_naive_0) :
    (function program "naive" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Evaluates.condition_int_compare hp rfl
  simpa [Int.toNat_of_nonneg nonnegative] using (naive.result n.toNat).returns

end data.«project-euler-statements».data.py.project_euler_statements.p5
