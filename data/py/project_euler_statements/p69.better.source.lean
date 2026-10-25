import data.«project-euler-statements».data.py.project_euler_statements.«p69.phi.source»

namespace data.«project-euler-statements».data.py.project_euler_statements.p69
open FormalSW.PyAst Calls ProjectEulerStatements
set_option Elab.async false

abbrev phiExpression (name : String) : Expr := .call (.name "phi") [.name name]
abbrev zeroCondition (name : String) : Expr :=
  .compare (phiExpression name) [(.eq, .constant (.int 0))]
abbrev zeroEither : Expr := .boolOp .or [zeroCondition "a", zeroCondition "b"]
abbrev productCondition : Expr :=
  .compare (.binOp (.name "a") .mult (phiExpression "b"))
    [(.gt, .binOp (.name "b") .mult (phiExpression "a"))]

theorem phi_expression_result (name : String) (n : Nat) (env : ScalarEnv)
    (found : env name = some (.int n)) :
    Evaluates program env (phiExpression name) (.int n.totient) :=
  Evaluates.call (.cons (Evaluates.lookup found) .nil) (phi.natural_result n)

theorem zero_condition_result (name : String) (n : Nat) (env : ScalarEnv)
    (found : env name = some (.int n)) :
    Evaluates program env (zeroCondition name) (.bool (decide (n.totient = 0))) :=
  Evaluates.compare (phi_expression_result name n env found) Evaluates.constant
    (by simp [scalarCompare, evalCmpOp])

theorem zero_either_result (a b : Nat) (env : ScalarEnv)
    (getA : env "a" = some (.int a)) (getB : env "b" = some (.int b)) :
    Evaluates program env zeroEither (.bool (decide (a.totient = 0 ∨ b.totient = 0))) := by
  have first := zero_condition_result "a" a env getA
  have second := zero_condition_result "b" b env getB
  by_cases zero : a.totient = 0
  · simpa only [zero, true_or, decide_true] using
      (Evaluates.boolean_stop (op := .or) (rest := [zeroCondition "b"])
        (by simpa only [zero, decide_true] using first) rfl)
  · apply Evaluates.boolean_continue
      (by simpa only [zero, decide_false] using first) rfl
    simpa only [zero, false_or] using Evaluates.boolean_last (op := .or) second

theorem product_condition_result (a b : Nat) (env : ScalarEnv)
    (getA : env "a" = some (.int a)) (getB : env "b" = some (.int b)) :
    Evaluates program env productCondition
      (.bool (decide (b * a.totient < a * b.totient))) := by
  apply Evaluates.compare (av := .int (a * b.totient)) (bv := .int (b * a.totient))
  · exact Evaluates.binary (Evaluates.lookup getA) (phi_expression_result "b" b env getB)
      (by simp [scalarBinary])
  · exact Evaluates.binary (Evaluates.lookup getB) (phi_expression_result "a" a env getA)
      (by simp [scalarBinary])
  · simp [scalarCompare, evalCmpOp]
    norm_cast

theorem better.result (a b : Nat) :
    ReturnsValue program "better" [.int a, .int b] (.bool (TotientMaximum.better a b)) := by
  let env := argumentEnv [⟨"a", some (.name "int"), none⟩, ⟨"b", some (.name "int"), none⟩]
    [.int a, .int b]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (zero_either_result a b env rfl rfl)
  by_cases zero : a.totient = 0 ∨ b.totient = 0
  · simpa only [scalarTruth, zero, decide_true, if_true, TotientMaximum.better] using
      (Evaluates.constant (module := program) (env := env) (value := .bool false))
  · simpa only [scalarTruth, zero, decide_false, if_false, TotientMaximum.better] using
      product_condition_result a b env rfl rfl

end data.«project-euler-statements».data.py.project_euler_statements.p69
