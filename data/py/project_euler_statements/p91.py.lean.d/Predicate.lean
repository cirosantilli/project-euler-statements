import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p91.py.ast»
import ProjectEulerSolutions.Lib.LatticeRightTriangles
import lang.py.FormalSW.Calls

namespace data.«project-euler-statements».data.py.project_euler_statements.p91
open FormalSW.PyAst Calls ProjectEulerSolutions.LatticeRightTriangles
set_option Elab.async false

abbrev program := P91Ast.module

private theorem difference (env : ScalarEnv) (left right : String) (a b : Int)
    (getA : env left = some (.int a)) (getB : env right = some (.int b)) :
    Evaluates program env
      (.ifExp (.compare (.name right) [(.gtE, .name left)])
        (.binOp (.name right) .sub (.name left)) (.binOp (.name left) .sub (.name right)))
      (.int (axisDistance a b)) := by
  have compared : Evaluates program env (.compare (.name right) [(.gtE, .name left)])
      (.bool (decide (a ≤ b))) :=
    Evaluates.compare (Evaluates.lookup getB) (Evaluates.lookup getA) rfl
  apply Evaluates.conditional compared
  by_cases order : a ≤ b
  · simpa [axisDistance, order, scalarTruth] using
      Evaluates.binary (Evaluates.lookup getB) (Evaluates.lookup getA) (show scalarBinary .sub (.int b) (.int a) = some (.ok (.int (b - a))) from rfl)
  · simpa [axisDistance, order, scalarTruth] using
      Evaluates.binary (Evaluates.lookup getA) (Evaluates.lookup getB) (show scalarBinary .sub (.int a) (.int b) = some (.ok (.int (a - b))) from rfl)

private theorem sum_squares (env : ScalarEnv) (left right : String) (a b : Int)
    (getA : env left = some (.int a)) (getB : env right = some (.int b)) :
    Evaluates program env
      (.binOp (.binOp (.name left) .mult (.name left)) .add (.binOp (.name right) .mult (.name right)))
      (.int (norm a b)) :=
  Evaluates.binary
    (Evaluates.binary (Evaluates.lookup getA) (Evaluates.lookup getA) rfl)
    (Evaluates.binary (Evaluates.lookup getB) (Evaluates.lookup getB) rfl) rfl

private theorem sum_equals (env : ScalarEnv) (left right target : String) (a b c : Int)
    (getA : env left = some (.int a)) (getB : env right = some (.int b))
    (getC : env target = some (.int c)) :
    Evaluates program env (.compare (.binOp (.name left) .add (.name right)) [(.eq, .name target)])
      (.bool (decide (a + b = c))) :=
  Evaluates.compare (Evaluates.binary (Evaluates.lookup getA) (Evaluates.lookup getB) rfl)
    (Evaluates.lookup getC) (by simp [scalarCompare, evalCmpOp])

private theorem or_three (env : ScalarEnv) (a b c : Expr) (p q r : Bool)
    (first : Evaluates program env a (.bool p))
    (second : Evaluates program env b (.bool q))
    (third : Evaluates program env c (.bool r)) :
    Evaluates program env (.boolOp .or [a, b, c]) (.bool (p || q || r)) := by
  cases p
  · apply Evaluates.boolean_continue first rfl
    cases q
    · exact Evaluates.boolean_continue second rfl (Evaluates.boolean_last third)
    · exact Evaluates.boolean_stop second rfl
  · exact Evaluates.boolean_stop first rfl

/-- The actual squared-length predicate agrees with the geometric test for all signed coordinates. -/
theorem is_right.result (a b c d : Int) :
    ReturnsValue program "is_right" [.int a, .int b, .int c, .int d] (.bool (isRight a b c d)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (difference _ "a" "c" a c rfl rfl)
  apply BlockReturns.assign (difference _ "b" "d" b d rfl rfl)
  apply BlockReturns.assign (sum_squares _ "a" "b" a b rfl rfl)
  apply BlockReturns.assign (sum_squares _ "dx" "dy" (axisDistance a c) (axisDistance b d) rfl rfl)
  apply BlockReturns.assign (sum_squares _ "c" "d" c d rfl rfl)
  apply BlockReturns.return_value
  simp only [isRight, Bool.decide_or, ← Bool.or_assoc]
  apply or_three
  · exact
      (sum_equals _ "dot1" "dot2" "dot3" (norm a b) (distance a b c d) (norm c d) rfl rfl rfl)
  · exact
      (sum_equals _ "dot1" "dot3" "dot2" (norm a b) (norm c d) (distance a b c d) rfl rfl rfl)
  · exact
      (sum_equals _ "dot2" "dot3" "dot1" (distance a b c d) (norm c d) (norm a b) rfl rfl rfl)

end data.«project-euler-statements».data.py.project_euler_statements.p91
