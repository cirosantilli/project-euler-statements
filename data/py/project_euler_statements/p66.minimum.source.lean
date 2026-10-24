import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p66.py.ast»
import ProjectEulerStatements.P66
import lang.py.FormalSW.Calls

namespace data.«project-euler-statements».data.py.project_euler_statements.p66
open FormalSW.PyAst Calls ProjectEulerStatements.PellMinimum
set_option Elab.async false
private abbrev program := P66Ast.module
private abbrev natural (n : Nat) : Constant := .int n
private abbrev flag (value : Bool) : Constant := .bool value

theorem isqrt_evaluates (n : Nat) (expression : Expr) (env : ScalarEnv)
    (evaluated : Evaluates program env expression (natural n)) :
    Evaluates program env (.call (.name "isqrt") [expression]) (natural (Nat.sqrt n)) := by
  have root_eq : Math.isqrt n = Nat.sqrt n := Nat.eq_sqrt.mpr (Math.isqrt_spec n)
  apply Evaluates.library_call (.cons evaluated .nil) rfl
  change some (Math.isqrtCall [.int n]) = _
  simp [Math.isqrtCall, root_eq, show ¬ (n : Int) < 0 by omega, natural]

theorem is_square.result (n : Nat) :
    ReturnsValue program "is_square" [natural n] (flag (decide (Nat.sqrt n * Nat.sqrt n = n))) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (isqrt_evaluates n _ _ (Evaluates.lookup rfl))
  apply BlockReturns.return_value
  apply Evaluates.compare (av := natural (Nat.sqrt n * Nat.sqrt n)) (bv := natural n)
  · exact Evaluates.binary (av := natural (Nat.sqrt n)) (bv := natural (Nat.sqrt n))
      (Evaluates.lookup rfl) (Evaluates.lookup rfl) (by simp [scalarBinary, natural])
  · exact Evaluates.lookup rfl
  · simp [scalarCompare, evalCmpOp]
    norm_cast

namespace minimal_x
def iteration : List Stmt :=
  [.assign [.name "x2"] (.binOp (.binOp (.binOp (.name "d") .mult (.name "y")) .mult (.name "y"))
    .add (.constant (.int 1))),
   .assign [.name "x"] (.call (.name "isqrt") [.name "x2"]),
   .ifThen (.compare (.binOp (.name "x") .mult (.name "x")) [(.eq, .name "x2")]) [.return (.name "x")] [],
   .augAssign (.name "y") .add (.constant (.int 1))]
def loop : Stmt := .whileDo (.constant (.bool true)) iteration []

/-- Existence of the least accepted y bounds the unbounded source loop's remaining work. -/
theorem loop_result (d y : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) (positive : 1 ≤ y)
    (before : y ≤ firstY d nonsquare) (env : ScalarEnv)
    (getD : env "d" = some (natural d)) (getY : env "y" = some (natural y)) :
    BlockReturns program env [loop] (natural (minimum d)) := by
  let square := d * y * y + 1
  let e1 := env.set "x2" (natural square)
  let e2 := e1.set "x" (natural (candidate d y))
  have tested : Evaluates program e2
      (.compare (.binOp (.name "x") .mult (.name "x")) [(.eq, .name "x2")])
      (flag (decide (candidate d y * candidate d y = square))) := by
    apply Evaluates.compare (av := natural (candidate d y * candidate d y)) (bv := natural square)
    · exact Evaluates.binary (av := natural (candidate d y)) (bv := natural (candidate d y))
        (Evaluates.lookup (by simp [e2, ScalarEnv.set])) (Evaluates.lookup (by simp [e2, ScalarEnv.set]))
        (by simp [scalarBinary, natural])
    · exact Evaluates.lookup (by simp [e2, e1, ScalarEnv.set])
    · simp [scalarCompare, evalCmpOp]
      norm_cast
  apply BlockReturns.while_loop (value := .bool true) Evaluates.constant
  apply BlockReturns.assign (value := natural square)
  · exact Evaluates.binary (av := natural (d * y * y)) (bv := natural 1)
      (Evaluates.binary (av := natural (d * y)) (bv := natural y)
        (Evaluates.binary (av := natural d) (bv := natural y)
          (Evaluates.lookup getD) (Evaluates.lookup getY) (by simp [scalarBinary, natural]))
        (Evaluates.lookup getY) (by simp [scalarBinary, natural]))
      Evaluates.constant (by simp [scalarBinary, natural, square])
  apply BlockReturns.assign (value := natural (candidate d y))
    (isqrt_evaluates square _ e1 (Evaluates.lookup (by simp [e1, ScalarEnv.set])))
  by_cases accepted : candidate d y * candidate d y = square
  · have same : y = firstY d nonsquare := by
      have minimal := firstY_le d y nonsquare ⟨positive, accepted⟩
      omega
    have answerEq : candidate d y = minimum d := by rw [minimum_of_nonsquare d nonsquare, same]
    apply BlockReturns.branch (value := .bool true) (by simpa only [accepted, decide_true] using tested)
    rw [← answerEq]
    exact BlockReturns.return_value (Evaluates.lookup (by simp [ScalarEnv.set]))
  · have more : y < firstY d nonsquare := by
      by_contra absent
      have same : y = firstY d nonsquare := by omega
      apply accepted
      exact (by simpa only [square, same] using (firstY_qualifies d nonsquare).2)
    apply BlockReturns.branch (value := .bool false) (by simpa only [accepted, decide_false] using tested)
    apply BlockReturns.augAssign (value := natural (y + 1))
      (Evaluates.binary (av := natural y) (bv := natural 1)
        (Evaluates.lookup (by simpa [e2, e1, ScalarEnv.set] using getY)) Evaluates.constant
        (by simp [scalarBinary, natural]))
    have rest := loop_result d (y + 1) nonsquare (by omega) (by omega)
      (e2.set "y" (natural (y + 1)))
      (by simpa [e2, e1, ScalarEnv.set] using getD) (by simp [ScalarEnv.set])
    simpa only [loopContinuation, show loopControl iteration = false from rfl,
      Bool.false_eq_true, if_false] using rest
termination_by firstY d nonsquare - y
decreasing_by omega

theorem result (d : Nat) : ReturnsValue program "minimal_x" [natural d] (natural (minimum d)) := by
  apply BlockReturns.function rfl rfl
  by_cases square : Nat.sqrt d * Nat.sqrt d = d
  · apply BlockReturns.branch (value := .bool true)
      (by simpa only [square, decide_true] using
        (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (is_square.result d)))
    rw [minimum_of_square d square]
    exact BlockReturns.return_value Evaluates.constant
  · apply BlockReturns.branch (value := .bool false)
      (by simpa only [square, decide_false] using
        (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (is_square.result d)))
    apply BlockReturns.assign (value := natural 1) Evaluates.constant
    exact loop_result d 1 square (by omega) (firstY_qualifies d square).1 _ rfl rfl

end minimal_x
end data.«project-euler-statements».data.py.project_euler_statements.p66
