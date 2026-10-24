import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p60.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerSolutions.Lib.DecimalShift
import FormalSW

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p60
open FormalSW.PyAst
private abbrev program := P60Ast.module

namespace pow10_for

def condition : Expr := .compare (.name "base") [(.ltE, .name "n")]
def body : List Stmt := [.augAssign (.name "base") .mult (.constant (.int 10))]
def code : List Stmt :=
  [.assign [.name "base"] (.constant (.int 1)), .whileDo condition body [], .return (.name "base")]

theorem code_source :
    executableBody ((findFunctionIn program.body "pow10_for").getD ([], [])).2 = code := rfl

end pow10_for
end data.«project-euler-statements».data.py.project_euler_statements.p60


namespace data.«project-euler-statements».data.py.project_euler_statements.p60.pow10_for.heap
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.DecimalShift
private abbrev program := P60Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
/-- The actual while loop terminates by its remaining positive gap, independently
of the decimal-digit specification. Multiplication changes only the local p. -/
theorem loop (n : Int) (p : Nat) (positive : 0 < p) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getP : env "base" = some (number p))
    (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    BlockReturns program env [.whileDo condition body [], .return (.name "base")]
      heap (number (decimalShiftFrom n p positive)) heap globals := by
  by_cases active : (p : Int) ≤ n
  · have nextPositive : 0 < p * 10 := by omega
    let nextEnv := HeapCalls.setLocal env "base" (number (p * 10))
    have nextN : nextEnv "n" = some (number n) := by
      simpa [nextEnv, HeapCalls.setLocal] using getN
    have nextP : nextEnv "base" = some (number (p * 10)) := by simp [nextEnv, HeapCalls.setLocal]
    have continued := loop n (p * 10) nextPositive nextEnv nextN nextP heap globals
    rw [from_step n p positive active]
    apply BlockReturns.while_loop (flag := true) (value := flag true) (middle := heap)
      (Evaluates.compare (Evaluates.lookup getP) (Evaluates.lookup getN)
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, active])) rfl
    apply BlockReturns.augAssign getP Evaluates.constant
      (value := number (p * 10)) (afterOperation := heap)
    · simp [HeapCalls.inplace, Mutable.binary, scalarBinary, number]
    · exact continued
  · rw [from_done n p positive (by omega)]
    apply BlockReturns.while_loop (flag := false) (value := flag false) (middle := heap)
      (Evaluates.compare (Evaluates.lookup getP) (Evaluates.lookup getN)
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, active])) rfl
    exact BlockReturns.return_value (Evaluates.lookup getP)
termination_by n.toNat + 1 - p
decreasing_by exact measure_step n p positive active

/-- Full actual Python function result, without a nonnegative-input precondition. -/
theorem result (n : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "pow10_for" [number n] heap (number (decimalShift n)) heap globals := by
  let params := ((findFunctionIn program.body "pow10_for").getD ([], [])).1
  let sourceBody := ((findFunctionIn program.body "pow10_for").getD ([], [])).2
  let env := HeapCalls.functionEnv params sourceBody [number n] globals
  have source : executableBody sourceBody = code := code_source
  apply BlockReturns.function rfl rfl
  change BlockReturns program env (executableBody sourceBody) heap (number (decimalShift n)) heap globals
  rw [source]
  apply BlockReturns.assign Evaluates.constant
  exact loop n 1 (by decide) (HeapCalls.setLocal env "base" (number 1))
    (by cases globals <;> rfl) (by rfl) heap globals


end data.«project-euler-statements».data.py.project_euler_statements.p60.pow10_for.heap

namespace data.«project-euler-statements».data.py.project_euler_statements.p60.pow10_for.pure
open FormalSW.PyAst
open ProjectEulerSolutions.DecimalShift
set_option Elab.async false
private abbrev program := P60Ast.module

/-- Scalar-call execution follows the same actual source and well-founded gap.
This supplies the runtime selected for pow10_for's public standalone marker. -/
theorem loop (n : Int) (p : Nat) (positive : 0 < p) (env : ScalarEnv)
    (getN : env "n" = some (.int n)) (getP : env "base" = some (.int p)) :
    Calls.BlockReturns program env [.whileDo condition body [], .return (.name "base")]
      (.int (decimalShiftFrom n p positive)) := by
  by_cases active : (p : Int) ≤ n
  · have nextPositive : 0 < p * 10 := by omega
    let nextEnv := env.set "base" (.int (p * 10))
    have nextN : nextEnv "n" = some (.int n) := by
      simpa [nextEnv, ScalarEnv.set] using getN
    have nextP : nextEnv "base" = some (.int (p * 10)) := by simp [nextEnv, ScalarEnv.set]
    have continued := loop n (p * 10) nextPositive nextEnv nextN nextP
    rw [from_step n p positive active]
    apply Calls.BlockReturns.while_loop (value := .bool true)
      (Calls.Evaluates.compare (Calls.Evaluates.lookup getP) (Calls.Evaluates.lookup getN)
        (by simp [scalarCompare, evalCmpOp, active]))
    apply Calls.BlockReturns.augAssign (value := .int ((p * 10 : Nat) : Int))
      (Calls.Evaluates.binary (Calls.Evaluates.lookup getP) Calls.Evaluates.constant
        (by simp [scalarBinary]))
    exact continued
  · rw [from_done n p positive (by omega)]
    apply Calls.BlockReturns.while_loop (value := .bool false)
      (Calls.Evaluates.compare (Calls.Evaluates.lookup getP) (Calls.Evaluates.lookup getN)
        (by simp [scalarCompare, evalCmpOp, active]))
    exact Calls.BlockReturns.return_value (Calls.Evaluates.lookup getP)
termination_by n.toNat + 1 - p
decreasing_by exact measure_step n p positive active

/-- Exact pure-call result for every signed integer input. -/
theorem result (n : Int) :
    Calls.ReturnsValue program "pow10_for" [.int n] (.int (decimalShift n)) := by
  let params := ((findFunctionIn program.body "pow10_for").getD ([], [])).1
  let sourceBody := ((findFunctionIn program.body "pow10_for").getD ([], [])).2
  let env := FormalSW.PyAst.argumentEnv params [.int n]
  have source : executableBody sourceBody = code := code_source
  apply Calls.BlockReturns.function rfl rfl
  change Calls.BlockReturns program env (executableBody sourceBody) (.int (decimalShift n))
  rw [source]
  apply Calls.BlockReturns.assign Calls.Evaluates.constant
  exact loop n 1 (by decide) (env.set "base" (.int 1)) (by rfl) (by rfl)

end data.«project-euler-statements».data.py.project_euler_statements.p60.pow10_for.pure

namespace data.«project-euler-statements».data.py.project_euler_statements.p60.pow10_for.legacy
open FormalSW.PyAst
open ProjectEulerSolutions.DecimalShift
set_option Elab.async false
private abbrev program := P60Ast.module

/-- The original small statement interpreter performs one guard step and one
multiplication step per active iteration; the same natural gap strictly falls. -/
theorem loop (n : Int) (p : Nat) (positive : 0 < p) (env : ScalarEnv)
    (getN : env "n" = some (.int n)) (getP : env "base" = some (.int p)) :
    Finishes scalarStep
      (⟨[.whileDo condition body [], .return (.name "base")], env⟩ : ScalarState)
      (.ok (.int (decimalShiftFrom n p positive))) := by
  by_cases active : (p : Int) ≤ n
  · have nextPositive : 0 < p * 10 := by omega
    let nextEnv := env.set "base" (.int ((p * 10 : Nat) : Int))
    have nextN : nextEnv "n" = some (.int n) := by
      simpa [nextEnv, ScalarEnv.set] using getN
    have nextP : nextEnv "base" = some (.int ((p * 10 : Nat) : Int)) := by simp [nextEnv, ScalarEnv.set]
    have continued := loop n (p * 10) nextPositive nextEnv nextN nextP
    have tested : scalarExpr env condition = some (.ok (.bool true)) := by
      simp [condition, scalarExpr, getP, getN, scalarCompare, evalCmpOp, active]
    have multiplied : scalarExpr env (.binOp (.name "base") .mult (.constant (.int 10))) =
        some (.ok (.int ((p * 10 : Nat) : Int))) := by
      simp [scalarExpr, getP, scalarBinary]
    rw [from_step n p positive active]
    apply Finishes.next (following :=
      ⟨[.augAssign (.name "base") .mult (.constant (.int 10)),
        .whileDo condition body [], .return (.name "base")], env⟩)
    · simp [scalarStep, tested, scalarTruth, body]
    · apply Finishes.next (following := ⟨[.whileDo condition body [], .return (.name "base")], nextEnv⟩)
      · simp only [scalarStep, multiplied, nextEnv]
      · exact continued
  · have tested : scalarExpr env condition = some (.ok (.bool false)) := by
      simp [condition, scalarExpr, getP, getN, scalarCompare, evalCmpOp, active]
    rw [from_done n p positive (by omega)]
    apply Finishes.next (following := ⟨[.return (.name "base")], env⟩)
    · simp [scalarStep, tested, scalarTruth]
    · exact Finishes.done (by simp [scalarStep, scalarExpr, getP])
termination_by n.toNat + 1 - p
decreasing_by exact measure_step n p positive active

/-- Actual source termination/result in the precise legacy runtime chosen by
standalone frontend coverage. This does not assume a Calls-to-scalar bridge. -/
theorem result (n : Int) :
    Finishes (FormalSW.PyAst.scalarFunction program "pow10_for" [.int n]).step
      (FormalSW.PyAst.scalarFunction program "pow10_for" [.int n]).initial (.ok (.int (decimalShift n))) := by
  let params := ((findFunctionIn program.body "pow10_for").getD ([], [])).1
  let sourceBody := ((findFunctionIn program.body "pow10_for").getD ([], [])).2
  let env := FormalSW.PyAst.argumentEnv params [.int n]
  have source : executableBody sourceBody = code := code_source
  change Finishes scalarStep (⟨executableBody sourceBody, env⟩ : ScalarState) (.ok (.int (decimalShift n)))
  rw [source]
  apply Finishes.next (following :=
    ⟨[.whileDo condition body [], .return (.name "base")], env.set "base" (.int 1)⟩)
  · rfl
  · exact loop n 1 (by decide) (env.set "base" (.int 1)) (by rfl) (by rfl)

end data.«project-euler-statements».data.py.project_euler_statements.p60.pow10_for.legacy


namespace data.«project-euler-statements».data.py.project_euler_statements.p60
open FormalSW.PyAst
open ProjectEulerSolutions.DecimalShift

theorem pow10_for.«Returns» (n : Int) :
    (FormalSW.PyAst.scalarFunction P60Ast.module "pow10_for" [.int n]).Returns :=
  ⟨.int (decimalShift n), pow10_for.legacy.result n⟩

end data.«project-euler-statements».data.py.project_euler_statements.p60

namespace data.«project-euler-statements».data.py.project_euler_statements.p60
open FormalSW.PyAst
open ProjectEulerSolutions.DecimalShift

def concatenated (left right : Int) : Int := left * (decimalShift right : Int) + right
def prime (n : Int) : Bool := decide (Nat.Prime n.toNat)
def compatible (left right : Int) : Bool :=
  prime (concatenated left right) && prime (concatenated right left)

private theorem common_extension : Calls.Extends program CommonAst.module := by
  have extension : Calls.Extends { body := program.body.take 5 ++ CommonAst.module.body } CommonAst.module := by
    apply Calls.Extends.prepend
    · intro name member
      change name ∈ ["pow10_for", "concat", "pair_ok", "naive"] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    · intro name member
      change name ∈ ([] : List String) at member
      simp at member
  exact ⟨extension.functions, extension.libraries⟩

private theorem common_heap_extension : HeapCalls.Extends program CommonAst.module :=
  .of_classless common_extension rfl

/-- The reference uses the actual imported trial-division routine, including
its early return on negative inputs. Its result is mathematical primality. -/
theorem prime_call (n : Int) : Calls.ReturnsValue program "is_prime" [.int n] (.bool (prime n)) := by
  by_cases nonnegative : 0 ≤ n
  · simpa [prime, Int.toNat_of_nonneg nonnegative] using
      (common.is_prime.result n.toNat).extend common_extension
  · have zero : n.toNat = 0 := by omega
    have returned : Calls.ReturnsValue program "is_prime" [.int n] (.bool false) := by
      apply Calls.BlockReturns.function rfl rfl
      apply Calls.BlockReturns.branch (value := .bool true)
      · exact Calls.Evaluates.compare (Calls.Evaluates.lookup rfl) Calls.Evaluates.constant
          (by simp [scalarCompare, evalCmpOp]; omega)
      · exact Calls.BlockReturns.return_value Calls.Evaluates.constant
    simpa [prime, zero] using returned

theorem prime_heap_call (n : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "is_prime" [.scalar (.int n)] heap
      (.scalar (.bool (prime n))) heap := by
  by_cases nonnegative : 0 ≤ n
  · simpa [prime, Int.toNat_of_nonneg nonnegative] using
      (common.is_prime.heap_result n.toNat heap).extend common_heap_extension
  · have zero : n.toNat = 0 := by omega
    have returned : HeapCalls.ReturnsValue program "is_prime" [.scalar (.int n)] heap
        (.scalar (.bool false)) heap := by
      apply HeapCalls.BlockReturns.function rfl rfl
      apply HeapCalls.BlockReturns.branch (flag := true) (value := .scalar (.bool true)) (middle := heap)
      · exact HeapCalls.Evaluates.compare (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant
          (by simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega)
      · rfl
      · exact HeapCalls.BlockReturns.return_value HeapCalls.Evaluates.constant
    simpa [prime, zero] using returned

theorem concat.result (left right : Int) :
    Calls.ReturnsValue program "concat" [.int left, .int right] (.int (concatenated left right)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.binary
    (Calls.Evaluates.binary (Calls.Evaluates.lookup rfl)
      (Calls.Evaluates.call (.cons (Calls.Evaluates.lookup rfl) .nil) (pow10_for.pure.result right)) rfl)
    (Calls.Evaluates.lookup rfl) rfl

theorem concat.heap_result (left right : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "concat" [.scalar (.int left), .scalar (.int right)] heap
      (.scalar (.int (concatenated left right))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  exact HeapCalls.Evaluates.binary
    (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl)
      (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) (pow10_for.heap.result right heap)) rfl)
    (HeapCalls.Evaluates.lookup rfl) rfl

theorem concat.«Returns» (left right : Int) :
    (Calls.function program "concat" [.int left, .int right]).Returns :=
  (concat.result left right).returns

theorem pair_ok.result (left right : Int) :
    Calls.ReturnsValue program "pair_ok" [.int left, .int right] (.bool (compatible left right)) := by
  let env := FormalSW.PyAst.argumentEnv ((findFunctionIn program.body "pair_ok").getD ([], [])).1
    [.int left, .int right]
  have forward : Calls.Evaluates program env
      (.call (.name "is_prime") [.call (.name "concat") [.name "left", .name "right"]])
      (.bool (prime (concatenated left right))) :=
    Calls.Evaluates.call (.cons (Calls.Evaluates.call
      (.cons (Calls.Evaluates.lookup rfl) (.cons (Calls.Evaluates.lookup rfl) .nil))
      (concat.result left right)) .nil) (prime_call (concatenated left right))
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  cases tested : prime (concatenated left right) with
  | false =>
      simp only [compatible, tested, Bool.false_and]
      exact Calls.Evaluates.boolean_stop (by simpa [tested] using forward) rfl
  | true =>
      simp only [compatible, tested, Bool.true_and]
      apply Calls.Evaluates.boolean_continue (by simpa [tested] using forward) rfl
      apply Calls.Evaluates.boolean_last
      exact Calls.Evaluates.call (.cons (Calls.Evaluates.call
        (.cons (Calls.Evaluates.lookup rfl) (.cons (Calls.Evaluates.lookup rfl) .nil))
        (concat.result right left)) .nil) (prime_call (concatenated right left))

theorem pair_ok.heap_result (left right : Int) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "pair_ok" [.scalar (.int left), .scalar (.int right)] heap
      (.scalar (.bool (compatible left right))) heap := by
  let env := HeapCalls.functionEnv ((findFunctionIn program.body "pair_ok").getD ([], [])).1
    ((findFunctionIn program.body "pair_ok").getD ([], [])).2
    [.scalar (.int left), .scalar (.int right)] []
  have forward : HeapCalls.Evaluates program env
      (.call (.name "is_prime") [.call (.name "concat") [.name "left", .name "right"]]) heap
      (.scalar (.bool (prime (concatenated left right)))) heap :=
    HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.call
      (.cons (HeapCalls.Evaluates.lookup rfl) (.cons (HeapCalls.Evaluates.lookup rfl) .nil))
      (concat.heap_result left right heap)) .nil) (prime_heap_call (concatenated left right) heap)
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  cases tested : prime (concatenated left right) with
  | false =>
      simp only [compatible, tested, Bool.false_and]
      exact HeapCalls.Evaluates.boolean_stop (flag := false) (by simpa [tested] using forward) rfl rfl
  | true =>
      simp only [compatible, tested, Bool.true_and]
      apply HeapCalls.Evaluates.boolean_next (flag := true) (by simpa [tested] using forward) rfl rfl
      apply HeapCalls.Evaluates.boolean_last (flag := prime (concatenated right left))
      · exact HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.call
          (.cons (HeapCalls.Evaluates.lookup rfl) (.cons (HeapCalls.Evaluates.lookup rfl) .nil))
          (concat.heap_result right left heap)) .nil) (prime_heap_call (concatenated right left) heap)
      · cases prime (concatenated right left) <;> rfl

theorem pair_ok.«Returns» (left right : Int) :
    (Calls.function program "pair_ok" [.int left, .int right]).Returns :=
  (pair_ok.result left right).returns

theorem compatible_iff (left right : Int) : compatible left right = true ↔
    Nat.Prime (concatenated left right).toNat ∧ Nat.Prime (concatenated right left).toNat := by
  simp [compatible, prime]

end data.«project-euler-statements».data.py.project_euler_statements.p60
