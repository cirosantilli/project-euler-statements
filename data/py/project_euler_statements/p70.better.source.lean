import data.«project-euler-statements».data.py.project_euler_statements.«p70.digits.source»
import ProjectEulerStatements.Lib.TotientPermutationMinimum

/-! The guarded, strict cross-multiplication comparison preserves the caller heap. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p70
open FormalSW.PyAst HeapCalls ProjectEulerStatements
set_option Elab.async false

abbrev phiExpression (name : String) : Expr := .call (.name "phi") [.name name]
abbrev zeroCondition (name : String) : Expr :=
  .compare (phiExpression name) [(.eq, .constant (.int 0))]
abbrev zeroEither : Expr := .boolOp .or [zeroCondition "a", zeroCondition "b"]
abbrev productCondition : Expr :=
  .compare (.binOp (.name "a") .mult (phiExpression "b"))
    [(.lt, .binOp (.name "b") .mult (phiExpression "a"))]

theorem phi_expression_result (name : String) (n : Nat) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (found : env name = some (number n)) :
    Evaluates program env (phiExpression name) heap (number n.totient) heap :=
  Evaluates.call (.cons (Evaluates.lookup found) .nil) (phi.heap_natural_result n heap)

theorem zero_condition_result (name : String) (n : Nat) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (found : env name = some (number n)) :
    Evaluates program env (zeroCondition name) heap (flag (decide (n.totient = 0))) heap :=
  Evaluates.compare (middle := heap) (afterRight := heap)
    (phi_expression_result name n heap env found) Evaluates.constant
    (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])

theorem zero_either_result (a b : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getA : env "a" = some (number a)) (getB : env "b" = some (number b)) :
    Evaluates program env zeroEither heap (flag (decide (a.totient = 0 ∨ b.totient = 0))) heap := by
  have first := zero_condition_result "a" a heap env getA
  have second := zero_condition_result "b" b heap env getB
  by_cases zero : a.totient = 0
  · simpa only [zero, true_or, decide_true] using
      (Evaluates.boolean_stop (op := .or) (rest := [zeroCondition "b"])
        (by simpa only [zero, decide_true] using first) rfl rfl)
  · apply Evaluates.boolean_next
      (by simpa only [zero, decide_false] using first) rfl rfl
    simpa only [zero, false_or] using Evaluates.boolean_last (op := .or) second rfl

theorem product_condition_result (a b : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getA : env "a" = some (number a)) (getB : env "b" = some (number b)) :
    Evaluates program env productCondition heap
      (flag (decide (a * b.totient < b * a.totient))) heap := by
  apply Evaluates.compare (av := number (a * b.totient : Nat))
    (bv := number (b * a.totient : Nat)) (middle := heap) (afterRight := heap)
  · exact Evaluates.binary (middle := heap) (afterRight := heap)
      (Evaluates.lookup getA) (phi_expression_result "b" b heap env getB)
      (by simp [Mutable.binary, scalarBinary])
  · exact Evaluates.binary (middle := heap) (afterRight := heap)
      (Evaluates.lookup getB) (phi_expression_result "a" a heap env getA)
      (by simp [Mutable.binary, scalarBinary])
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    norm_cast

theorem better.result (a b : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "better" [number a, number b] heap
      (flag (TotientPermutation.better a b)) heap := by
  let env := HeapCalls.argumentEnv
    [⟨"a", some (.name "int"), none⟩, ⟨"b", some (.name "int"), none⟩] [number a, number b]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (zero_either_result a b heap env rfl rfl) rfl
  by_cases zero : a.totient = 0 ∨ b.totient = 0
  · simpa only [zero, decide_true, if_true, TotientPermutation.better] using
      (Evaluates.constant (module := program) (env := env) (heap := heap) (value := .bool false))
  · simpa only [zero, decide_false, if_false, TotientPermutation.better] using
      product_condition_result a b heap env rfl rfl

end data.«project-euler-statements».data.py.project_euler_statements.p70
