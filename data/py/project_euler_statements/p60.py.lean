import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p60.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerSolutions.Lib.DecimalShift
import ProjectEulerSolutions.Lib.CliqueSearch
import ProjectEulerSolutions.Lib.HeapRangeFold
import ProjectEulerSolutions.Lib.HeapSequenceFold
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


namespace data.«project-euler-statements».data.py.project_euler_statements.p60.naive
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
private abbrev program := P60Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private def numbers (values : List Nat) : List Mutable.Value := values.map (fun (p : Nat) => number p)

def code : List Stmt := executableBody ((findFunctionIn program.body "naive").getD ([], [])).2
private def nextBody (body : List Stmt) : List Stmt := match (body[0]? : Option Stmt) with
  | some (.forIn _ _ nested _) => nested
  | some (.ifThen _ yes _) => match (yes[0]? : Option Stmt) with
      | some (.forIn _ _ nested _) => nested
      | _ => []
  | _ => []
def loopBody : Nat → List Stmt
  | 0 => match (code[3]? : Option Stmt) with | some (.forIn _ _ body _) => body | _ => []
  | level + 1 => nextBody (loopBody level)
def guardAt (level : Nat) : Expr := match ((loopBody level)[0]? : Option Stmt) with
  | some (.ifThen guard _ _) => guard
  | _ => .constant (.bool true)
def leafCode : List Stmt := match ((loopBody 4)[0]? : Option Stmt) with
  | some (.ifThen _ yes _) => yes
  | _ => []

def totalExpression : Expr :=
  .binOp (.binOp (.binOp (.binOp (.name "a") .add (.name "b")) .add (.name "c")) .add (.name "d")) .add (.name "e")
def selectedExpression : Expr := .list [.name "a", .name "b", .name "c", .name "d", .name "e"]
def improveTest : Expr := .compare (.name "total") [(.lt, .name "best_sum")]
def improveCode : List Stmt :=
  [.assign [.name "best_sum"] (.name "total"), .assign [.name "best_set"] selectedExpression]
theorem leafCode_source : leafCode =
    [.assign [.name "total"] totalExpression, .ifThen improveTest improveCode []] := rfl

structure BestState (heap : Mutable.Heap) (env : HeapCalls.Env) (best : CliqueSearch.Best) where
  selectedAddress : Nat
  getSum : env "best_sum" = some (number best.bound)
  getSet : env "best_set" = some (.ref selectedAddress)
  found : heap[selectedAddress]? = some (.list (numbers best.chosen))

def BestState.bind {heap : Mutable.Heap} {env : HeapCalls.Env} {best : CliqueSearch.Best}
    (state : BestState heap env best) (name : String) (value : Mutable.Value)
    (notSum : name ≠ "best_sum") (notSet : name ≠ "best_set") : BestState heap (setLocal env name value) best where
  selectedAddress := state.selectedAddress
  getSum := by simpa [setLocal, Ne.symm notSum] using state.getSum
  getSet := by simpa [setLocal, Ne.symm notSet] using state.getSet
  found := state.found

def leafTotal (a b c d e : Nat) : Int := (a : Int) + b + c + d + e
theorem leafTotal_sum (a b c d e : Nat) : leafTotal a b c d e = ([a, b, c, d, e].sum : Int) := by
  simp [leafTotal, Int.add_assoc]

theorem leaf_result (heap : Mutable.Heap) (env : HeapCalls.Env) (best : CliqueSearch.Best)
    (state : BestState heap env best) (a b c d e : Nat)
    (getA : env "a" = some (number a)) (getB : env "b" = some (number b))
    (getC : env "c" = some (number c)) (getD : env "d" = some (number d))
    (getE : env "e" = some (number e)) :
    ∃ afterEnv finalHeap,
      ∃ _after : BestState finalHeap afterEnv (CliqueSearch.improve [a, b, c, d, e] (leafTotal a b c d e) best),
      BlockContinues program env leafCode heap afterEnv finalHeap ∧
      (∃ extra, finalHeap = heap ++ extra) ∧ HeapRangeFold.Frame ["total", "best_sum", "best_set"] env afterEnv := by
  let total := leafTotal a b c d e
  let counted := setLocal env "total" (number total)
  have totalEval : Evaluates program env totalExpression heap (number total) heap :=
    Evaluates.binary (Evaluates.binary (Evaluates.binary
      (Evaluates.binary (Evaluates.lookup getA) (Evaluates.lookup getB) rfl)
      (Evaluates.lookup getC) rfl) (Evaluates.lookup getD) rfl) (Evaluates.lookup getE) rfl
  have countedState := state.bind "total" (number total) (by decide) (by decide)
  have getTotal : counted "total" = some (number total) := by simp [counted, setLocal]
  have tested : Evaluates program counted improveTest heap (flag (decide (total < best.bound))) heap :=
    Evaluates.compare (Evaluates.lookup getTotal) (Evaluates.lookup countedState.getSum) rfl
  have countRun : BlockContinues program env [.assign [.name "total"] totalExpression] heap counted heap :=
    BlockContinues.assign totalEval
  by_cases improves : total < best.bound
  · have model : CliqueSearch.improve [a, b, c, d, e] (leafTotal a b c d e) best = ⟨total, [a, b, c, d, e]⟩ := by
      change (if total < best.bound then ⟨total, [a, b, c, d, e]⟩ else best) = _
      rw [if_pos improves]
    rw [model]
    let written := setLocal counted "best_sum" (number total)
    let selected := setLocal written "best_set" (.ref heap.length)
    let finalHeap := heap ++ [Mutable.Object.list (numbers [a, b, c, d, e])]
    let after : BestState finalHeap selected ⟨total, [a, b, c, d, e]⟩ := {
      selectedAddress := heap.length
      getSum := by simp [selected, written, setLocal]
      getSet := by simp [selected, setLocal]
      found := by simp [finalHeap] }
    refine ⟨selected, finalHeap, after, ?_, ⟨_, rfl⟩, ?_⟩
    · rw [leafCode_source]
      apply countRun.append
      apply BlockContinues.branch (by simpa only [improves, decide_true] using tested) rfl
      have first : BlockContinues program counted [improveCode[0]'(by decide)] heap written heap :=
        BlockContinues.assign (Evaluates.lookup getTotal)
      have second : BlockContinues program written [improveCode[1]'(by decide)] heap selected finalHeap := by
        apply BlockContinues.assign
        exact Evaluates.list
          (.cons (Evaluates.lookup (by simpa [written, counted, setLocal] using getA))
            (.cons (Evaluates.lookup (by simpa [written, counted, setLocal] using getB))
              (.cons (Evaluates.lookup (by simpa [written, counted, setLocal] using getC))
                (.cons (Evaluates.lookup (by simpa [written, counted, setLocal] using getD))
                  (.cons (Evaluates.lookup (by simpa [written, counted, setLocal] using getE)) .nil)))))
      exact first.append second
    · exact (HeapRangeFold.Frame.updated _ env "total" _ (by simp)).trans
        ((HeapRangeFold.Frame.updated _ counted "best_sum" _ (by simp)).trans
          (HeapRangeFold.Frame.updated _ written "best_set" _ (by simp)))
  · have model : CliqueSearch.improve [a, b, c, d, e] (leafTotal a b c d e) best = best := by
      change (if total < best.bound then ⟨total, [a, b, c, d, e]⟩ else best) = best
      rw [if_neg improves]
    rw [model]
    refine ⟨counted, heap, countedState, ?_, ⟨[], by simp⟩, HeapRangeFold.Frame.updated _ env "total" _ (by simp)⟩
    rw [leafCode_source]
    exact countRun.append (BlockContinues.branch (by simpa only [improves, decide_false] using tested) rfl .nil)

def Reads (env : HeapCalls.Env) (names : List String) (values : List Nat) : Prop :=
  List.Forall₂ (fun name (value : Nat) => env name = some (number value)) names values
def pairExpressions (names : List String) (target : String) : List Expr :=
  names.map (fun name => .call (.name "pair_ok") [.name name, .name target])

theorem pairs_evaluate (heap : Mutable.Heap) (env : HeapCalls.Env) (names : List String) (values : List Nat)
    (target : String) (value : Nat) (reads : Reads env names values) (getTarget : env target = some (number value)) :
    List.Forall₂ (fun expression answer => Evaluates program env expression heap (flag answer) heap)
      (pairExpressions names target) (values.map (fun (p : Nat) => compatible p value)) := by
  induction reads with
  | nil => exact .nil
  | @cons name p names values found rest ih =>
    exact .cons (Evaluates.call (.cons (Evaluates.lookup found) (.cons (Evaluates.lookup getTarget) .nil))
      (pair_ok.heap_result p value heap)) ih

private theorem and_evaluates (heap : Mutable.Heap) (env : HeapCalls.Env) (first : Expr) (answer : Bool)
    (head : Evaluates program env first heap (flag answer) heap)
    (expressions : List Expr) (answers : List Bool)
    (rest : List.Forall₂ (fun expression answer => Evaluates program env expression heap (flag answer) heap) expressions answers) :
    Evaluates program env (.boolOp .and (first :: expressions)) heap (flag ((answer :: answers).all id)) heap := by
  induction rest generalizing first answer with
  | nil =>
    simpa using Evaluates.boolean_last (flag := answer) head (by cases answer <;> rfl)
  | cons evaluated rest ih =>
    cases answer with
    | false =>
      simpa using Evaluates.boolean_stop (op := .and) (flag := false) head rfl rfl
    | true =>
      simpa using Evaluates.boolean_next (op := .and) (flag := true) head rfl rfl (ih _ _ evaluated)

def guardFor (previous target : String) (earlier : List String) : Expr :=
  .boolOp .and (.compare (.name previous) [(.lt, .name target)] :: pairExpressions earlier target)

theorem guard_b_source : guardAt 1 = guardFor "a" "b" ["a"] := rfl
theorem guard_c_source : guardAt 2 = guardFor "b" "c" ["a", "b"] := rfl
theorem guard_d_source : guardAt 3 = guardFor "c" "d" ["a", "b", "c"] := rfl
theorem guard_e_source : guardAt 4 = guardFor "d" "e" ["a", "b", "c", "d"] := rfl

theorem guard_evaluates (heap : Mutable.Heap) (env : HeapCalls.Env) (previous target : String)
    (earlier : List String) (values : List Nat) (left right : Nat)
    (getLeft : env previous = some (number left)) (getRight : env target = some (number right))
    (reads : Reads env earlier values) :
    Evaluates program env (guardFor previous target earlier) heap
      (flag (decide (left < right) && values.all (fun (p : Nat) => compatible p right))) heap := by
  have comparison : Evaluates program env (.compare (.name previous) [(.lt, .name target)])
      heap (flag (decide (left < right))) heap :=
    Evaluates.compare (Evaluates.lookup getLeft) (Evaluates.lookup getRight)
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  simpa only [List.all_cons, List.all_map, Function.comp_def, id_eq] using and_evaluates heap env _ _ comparison
    (pairExpressions earlier target) _ (pairs_evaluate heap env earlier values target right reads getRight)

structure Prefix4 (env : HeapCalls.Env) (a b c d : Nat) : Prop where
  getA : env "a" = some (number a)
  getB : env "b" = some (number b)
  getC : env "c" = some (number c)
  getD : env "d" = some (number d)

theorem Prefix4.bind_e {env : HeapCalls.Env} {a b c d : Nat} (values : Prefix4 env a b c d) (e : Nat) :
    Prefix4 (setLocal env "e" (number e)) a b c d :=
  ⟨by simpa [setLocal] using values.getA, by simpa [setLocal] using values.getB,
   by simpa [setLocal] using values.getC, by simpa [setLocal] using values.getD⟩

theorem Prefix4.after_leaf {env afterEnv : HeapCalls.Env} {a b c d : Nat}
    (values : Prefix4 env a b c d) (frame : HeapRangeFold.Frame ["total", "best_sum", "best_set"] env afterEnv) :
    Prefix4 afterEnv a b c d :=
  ⟨(frame "a" (by simp)).trans values.getA, (frame "b" (by simp)).trans values.getB,
   (frame "c" (by simp)).trans values.getC, (frame "d" (by simp)).trans values.getD⟩

def acceptedE (a b c d e : Nat) : Bool :=
  decide (d < e) && [a, b, c, d].all (fun (p : Nat) => compatible p e)
def updateE (a b c d : Nat) (best : CliqueSearch.Best) (e : Nat) : CliqueSearch.Best :=
  if acceptedE a b c d e then CliqueSearch.improve [a, b, c, d, e] (leafTotal a b c d e) best else best

theorem loopBody_e_source : loopBody 4 = [.ifThen (guardFor "d" "e" ["a", "b", "c", "d"]) leafCode []] := rfl
def eLoopCode : List Stmt := match ((loopBody 3)[0]? : Option Stmt) with
  | some (.ifThen _ yes _) => yes
  | _ => []
theorem eLoopCode_source : eLoopCode = [.forIn (.name "e") (.name "primes") (loopBody 4) []] := rfl

/-- All iterations of the actual innermost reference loop, preserving each
short-circuit pair test, the original iterable, and equal-sum tie behavior. -/
theorem e_loop_result (heap : Mutable.Heap) (env : HeapCalls.Env) (best : CliqueSearch.Best)
    (state : BestState heap env best) (a b c d : Nat) (values : Prefix4 env a b c d)
    (primeAddress : Nat) (primes : List Nat) (getPrimes : env "primes" = some (.ref primeAddress))
    (found : heap[primeAddress]? = some (.list (numbers primes))) :
    ∃ afterEnv finalHeap,
      ∃ _after : BestState finalHeap afterEnv (primes.foldl (updateE a b c d) best),
      BlockContinues program env eLoopCode heap afterEnv finalHeap ∧ Prefix4 afterEnv a b c d ∧
      (∃ extra, finalHeap = heap ++ extra) ∧ HeapRangeFold.Frame ["e", "total", "best_sum", "best_set"] env afterEnv := by
  let invariant : Mutable.Heap → HeapCalls.Env → CliqueSearch.Best → Prop := fun heap env best =>
    ∃ _state : BestState heap env best, Prefix4 env a b c d
  have bindInvariant : ∀ heap env best e, invariant heap env best → e ∈ primes →
      invariant heap (setLocal env "e" (number e)) best := by
    intro heap env best e safe _
    rcases safe with ⟨state, values⟩
    exact ⟨state.bind "e" (number e) (by decide) (by decide), values.bind_e e⟩
  have cell : ∀ heap env best e, invariant heap env best → e ∈ primes → env "e" = some (number e) →
      ∃ afterEnv finalHeap, BlockContinues program env (loopBody 4) heap afterEnv finalHeap ∧
        invariant finalHeap afterEnv (updateE a b c d best e) ∧
        (∃ extra, finalHeap = heap ++ extra) ∧ HeapRangeFold.Frame ["e", "total", "best_sum", "best_set"] env afterEnv := by
    intro heap env best e safe _ getE
    rcases safe with ⟨state, values⟩
    have reads : Reads env ["a", "b", "c", "d"] [a, b, c, d] :=
      .cons values.getA (.cons values.getB (.cons values.getC (.cons values.getD .nil)))
    have tested : Evaluates program env (guardFor "d" "e" ["a", "b", "c", "d"])
        heap (flag (acceptedE a b c d e)) heap :=
      guard_evaluates heap env "d" "e" ["a", "b", "c", "d"] [a, b, c, d] d e values.getD getE reads
    cases accepted : acceptedE a b c d e with
    | false =>
      refine ⟨env, heap, ?_, ?_, ⟨[], by simp⟩, HeapRangeFold.Frame.refl _ env⟩
      · rw [loopBody_e_source]
        exact BlockContinues.branch (flag := false) (by simpa only [accepted] using tested) rfl .nil
      · exact ⟨by simpa only [updateE, accepted, Bool.false_eq_true, if_false] using state, values⟩
    | true =>
      obtain ⟨afterEnv, finalHeap, after, executed, extra, frame⟩ := leaf_result heap env best state a b c d e
        values.getA values.getB values.getC values.getD getE
      refine ⟨afterEnv, finalHeap, ?_, ?_, extra, ?_⟩
      · rw [loopBody_e_source]
        exact BlockContinues.branch (flag := true) (by simpa only [accepted] using tested) rfl executed
      · exact ⟨by simpa only [updateE, accepted, if_true] using after, values.after_leaf frame⟩
      · intro name outside
        exact frame name (fun inside => outside (List.mem_cons_of_mem "e" inside))
  obtain ⟨afterEnv, finalHeap, executed, ⟨after, finalValues⟩, extra, frame⟩ :=
    HeapSequenceFold.for_list program "e" (loopBody 4) rfl ["e", "total", "best_sum", "best_set"] (by simp)
      (fun (e : Nat) => number e) (updateE a b c d) invariant primeAddress primes bindInvariant cell heap env best
      ⟨state, values⟩ (.name "primes") (by intros; simp) (Evaluates.lookup getPrimes) found
  exact ⟨afterEnv, finalHeap, after, by simpa only [eLoopCode_source] using executed, finalValues, extra, frame⟩


structure PrimeState (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat) (primes : List Nat) : Prop where
  getPrimes : env "primes" = some (.ref address)
  found : heap[address]? = some (.list (numbers primes))

theorem PrimeState.bind {heap : Mutable.Heap} {env : HeapCalls.Env} {address : Nat} {primes : List Nat}
    (input : PrimeState heap env address primes) (name : String) (value : Mutable.Value) (different : "primes" ≠ name) :
    PrimeState heap (setLocal env name value) address primes :=
  ⟨by simpa [setLocal, different] using input.getPrimes, input.found⟩

theorem PrimeState.after {heap finalHeap : Mutable.Heap} {env afterEnv : HeapCalls.Env} {address : Nat} {primes : List Nat}
    (input : PrimeState heap env address primes) (changed : List String)
    (extra : ∃ extra, finalHeap = heap ++ extra) (frame : HeapRangeFold.Frame changed env afterEnv)
    (notWritten : "primes" ∉ changed) : PrimeState finalHeap afterEnv address primes := by
  refine ⟨(frame "primes" notWritten).trans input.getPrimes, ?_⟩
  obtain ⟨extra, same⟩ := extra
  rw [same]
  exact HeapCollection.prefix_found heap extra _ _ input.found


structure Prefix3 (env : HeapCalls.Env) (a b c : Nat) : Prop where
  getA : env "a" = some (number a)
  getB : env "b" = some (number b)
  getC : env "c" = some (number c)

theorem Prefix3.bind_d {env : HeapCalls.Env} {a b c : Nat} (values : Prefix3 env a b c) (d : Nat) :
    Prefix3 (setLocal env "d" (number d)) a b c := ⟨by simpa [setLocal] using values.getA, by simpa [setLocal] using values.getB, by simpa [setLocal] using values.getC⟩

def acceptedD (a b c d : Nat) : Bool :=
  decide (c < d) && [a, b, c].all (fun (p : Nat) => compatible p d)
def updateD (primes : List Nat) (a b c : Nat) (best : CliqueSearch.Best) (d : Nat) : CliqueSearch.Best :=
  if acceptedD a b c d then primes.foldl (updateE a b c d) best else best

theorem loopBody_d_source : loopBody 3 = [.ifThen (guardFor "c" "d" ["a", "b", "c"]) eLoopCode []] := rfl
def dLoopCode : List Stmt := match ((loopBody 2)[0]? : Option Stmt) with
  | some (.ifThen _ yes _) => yes
  | some (.forIn _ _ _ _) => loopBody 2
  | _ => []
theorem dLoopCode_source : dLoopCode = [.forIn (.name "d") (.name "primes") (loopBody 3) []] := rfl

theorem d_loop_result (heap : Mutable.Heap) (env : HeapCalls.Env) (best : CliqueSearch.Best)
    (state : BestState heap env best) (a b c : Nat) (values : Prefix3 env a b c)
    (primeAddress : Nat) (primes : List Nat) (input : PrimeState heap env primeAddress primes) :
    ∃ afterEnv finalHeap,
      ∃ _after : BestState finalHeap afterEnv (primes.foldl (updateD primes a b c) best),
      BlockContinues program env dLoopCode heap afterEnv finalHeap ∧ Prefix3 afterEnv a b c ∧
      (∃ extra, finalHeap = heap ++ extra) ∧ HeapRangeFold.Frame ["d", "e", "total", "best_sum", "best_set"] env afterEnv := by
  let invariant : Mutable.Heap → HeapCalls.Env → CliqueSearch.Best → Prop := fun heap env best =>
    ∃ _state : BestState heap env best, Prefix3 env a b c ∧ PrimeState heap env primeAddress primes
  have bindInvariant : ∀ heap env best d, invariant heap env best → d ∈ primes →
      invariant heap (setLocal env "d" (number d)) best := by
    intro heap env best d safe _
    rcases safe with ⟨state, values, input⟩
    exact ⟨state.bind "d" (number d) (by decide) (by decide), values.bind_d d, input.bind "d" (number d) (by decide)⟩
  have test : ∀ heap env best d, invariant heap env best → d ∈ primes → env "d" = some (number d) →
      Evaluates program env (guardFor "c" "d" ["a", "b", "c"]) heap (flag (acceptedD a b c d)) heap := by
    intro heap env best d safe _ getD
    rcases safe with ⟨state, values, input⟩
    exact guard_evaluates heap env "c" "d" ["a", "b", "c"] [a, b, c] c d values.getC getD
      (.cons values.getA (.cons values.getB (.cons values.getC (.nil))))
  have cell : ∀ heap env best d, invariant heap env best → d ∈ primes → env "d" = some (number d) →
      ∃ afterEnv finalHeap, BlockContinues program env eLoopCode heap afterEnv finalHeap ∧
        invariant finalHeap afterEnv (primes.foldl (updateE a b c d) best) ∧
        (∃ extra, finalHeap = heap ++ extra) ∧ HeapRangeFold.Frame ["d", "e", "total", "best_sum", "best_set"] env afterEnv := by
    intro heap env best d safe _ getD
    rcases safe with ⟨state, values, input⟩
    obtain ⟨afterEnv, finalHeap, after, executed, finalValues, extra, frame⟩ :=
      e_loop_result heap env best state a b c d ⟨values.getA, values.getB, values.getC, getD⟩ primeAddress primes input.getPrimes input.found
    refine ⟨afterEnv, finalHeap, executed, ⟨after, ⟨finalValues.getA, finalValues.getB, finalValues.getC⟩, input.after ["e", "total", "best_sum", "best_set"] extra frame (by simp)⟩, extra, ?_⟩
    intro name outside
    exact frame name (fun inside => outside (List.mem_cons_of_mem "d" inside))
  obtain ⟨afterEnv, finalHeap, executed, ⟨after, finalValues, _⟩, extra, frame⟩ :=
    HeapSequenceFold.for_guarded_list program "d" (guardFor "c" "d" ["a", "b", "c"]) eLoopCode rfl
      ["d", "e", "total", "best_sum", "best_set"] (by simp) (fun (d : Nat) => number d) (acceptedD a b c)
      (fun best d => primes.foldl (updateE a b c d) best)
      invariant primeAddress primes bindInvariant test cell heap env best ⟨state, values, input⟩
      (.name "primes") (by intros; simp) (Evaluates.lookup input.getPrimes) input.found
  exact ⟨afterEnv, finalHeap, after, by simpa only [dLoopCode_source, loopBody_d_source] using executed, finalValues, extra, frame⟩


structure Prefix2 (env : HeapCalls.Env) (a b : Nat) : Prop where
  getA : env "a" = some (number a)
  getB : env "b" = some (number b)

theorem Prefix2.bind_c {env : HeapCalls.Env} {a b : Nat} (values : Prefix2 env a b) (c : Nat) :
    Prefix2 (setLocal env "c" (number c)) a b := ⟨by simpa [setLocal] using values.getA, by simpa [setLocal] using values.getB⟩

def acceptedC (a b c : Nat) : Bool :=
  decide (b < c) && [a, b].all (fun (p : Nat) => compatible p c)
def updateC (primes : List Nat) (a b : Nat) (best : CliqueSearch.Best) (c : Nat) : CliqueSearch.Best :=
  if acceptedC a b c then primes.foldl (updateD primes a b c) best else best

theorem loopBody_c_source : loopBody 2 = [.ifThen (guardFor "b" "c" ["a", "b"]) dLoopCode []] := rfl
def cLoopCode : List Stmt := match ((loopBody 1)[0]? : Option Stmt) with
  | some (.ifThen _ yes _) => yes
  | some (.forIn _ _ _ _) => loopBody 1
  | _ => []
theorem cLoopCode_source : cLoopCode = [.forIn (.name "c") (.name "primes") (loopBody 2) []] := rfl

theorem c_loop_result (heap : Mutable.Heap) (env : HeapCalls.Env) (best : CliqueSearch.Best)
    (state : BestState heap env best) (a b : Nat) (values : Prefix2 env a b)
    (primeAddress : Nat) (primes : List Nat) (input : PrimeState heap env primeAddress primes) :
    ∃ afterEnv finalHeap,
      ∃ _after : BestState finalHeap afterEnv (primes.foldl (updateC primes a b) best),
      BlockContinues program env cLoopCode heap afterEnv finalHeap ∧ Prefix2 afterEnv a b ∧
      (∃ extra, finalHeap = heap ++ extra) ∧ HeapRangeFold.Frame ["c", "d", "e", "total", "best_sum", "best_set"] env afterEnv := by
  let invariant : Mutable.Heap → HeapCalls.Env → CliqueSearch.Best → Prop := fun heap env best =>
    ∃ _state : BestState heap env best, Prefix2 env a b ∧ PrimeState heap env primeAddress primes
  have bindInvariant : ∀ heap env best c, invariant heap env best → c ∈ primes →
      invariant heap (setLocal env "c" (number c)) best := by
    intro heap env best c safe _
    rcases safe with ⟨state, values, input⟩
    exact ⟨state.bind "c" (number c) (by decide) (by decide), values.bind_c c, input.bind "c" (number c) (by decide)⟩
  have test : ∀ heap env best c, invariant heap env best → c ∈ primes → env "c" = some (number c) →
      Evaluates program env (guardFor "b" "c" ["a", "b"]) heap (flag (acceptedC a b c)) heap := by
    intro heap env best c safe _ getC
    rcases safe with ⟨state, values, input⟩
    exact guard_evaluates heap env "b" "c" ["a", "b"] [a, b] b c values.getB getC
      (.cons values.getA (.cons values.getB (.nil)))
  have cell : ∀ heap env best c, invariant heap env best → c ∈ primes → env "c" = some (number c) →
      ∃ afterEnv finalHeap, BlockContinues program env dLoopCode heap afterEnv finalHeap ∧
        invariant finalHeap afterEnv (primes.foldl (updateD primes a b c) best) ∧
        (∃ extra, finalHeap = heap ++ extra) ∧ HeapRangeFold.Frame ["c", "d", "e", "total", "best_sum", "best_set"] env afterEnv := by
    intro heap env best c safe _ getC
    rcases safe with ⟨state, values, input⟩
    obtain ⟨afterEnv, finalHeap, after, executed, finalValues, extra, frame⟩ :=
      d_loop_result heap env best state a b c ⟨values.getA, values.getB, getC⟩ primeAddress primes input
    refine ⟨afterEnv, finalHeap, executed, ⟨after, ⟨finalValues.getA, finalValues.getB⟩, input.after ["d", "e", "total", "best_sum", "best_set"] extra frame (by simp)⟩, extra, ?_⟩
    intro name outside
    exact frame name (fun inside => outside (List.mem_cons_of_mem "c" inside))
  obtain ⟨afterEnv, finalHeap, executed, ⟨after, finalValues, _⟩, extra, frame⟩ :=
    HeapSequenceFold.for_guarded_list program "c" (guardFor "b" "c" ["a", "b"]) dLoopCode rfl
      ["c", "d", "e", "total", "best_sum", "best_set"] (by simp) (fun (c : Nat) => number c) (acceptedC a b)
      (fun best c => primes.foldl (updateD primes a b c) best)
      invariant primeAddress primes bindInvariant test cell heap env best ⟨state, values, input⟩
      (.name "primes") (by intros; simp) (Evaluates.lookup input.getPrimes) input.found
  exact ⟨afterEnv, finalHeap, after, by simpa only [cLoopCode_source, loopBody_c_source] using executed, finalValues, extra, frame⟩


structure Prefix1 (env : HeapCalls.Env) (a : Nat) : Prop where
  getA : env "a" = some (number a)

theorem Prefix1.bind_b {env : HeapCalls.Env} {a : Nat} (values : Prefix1 env a) (b : Nat) :
    Prefix1 (setLocal env "b" (number b)) a := ⟨by simpa [setLocal] using values.getA⟩

def acceptedB (a b : Nat) : Bool :=
  decide (a < b) && [a].all (fun (p : Nat) => compatible p b)
def updateB (primes : List Nat) (a : Nat) (best : CliqueSearch.Best) (b : Nat) : CliqueSearch.Best :=
  if acceptedB a b then primes.foldl (updateC primes a b) best else best

theorem loopBody_b_source : loopBody 1 = [.ifThen (guardFor "a" "b" ["a"]) cLoopCode []] := rfl
def bLoopCode : List Stmt := match ((loopBody 0)[0]? : Option Stmt) with
  | some (.ifThen _ yes _) => yes
  | some (.forIn _ _ _ _) => loopBody 0
  | _ => []
theorem bLoopCode_source : bLoopCode = [.forIn (.name "b") (.name "primes") (loopBody 1) []] := rfl

theorem b_loop_result (heap : Mutable.Heap) (env : HeapCalls.Env) (best : CliqueSearch.Best)
    (state : BestState heap env best) (a : Nat) (values : Prefix1 env a)
    (primeAddress : Nat) (primes : List Nat) (input : PrimeState heap env primeAddress primes) :
    ∃ afterEnv finalHeap,
      ∃ _after : BestState finalHeap afterEnv (primes.foldl (updateB primes a) best),
      BlockContinues program env bLoopCode heap afterEnv finalHeap ∧ Prefix1 afterEnv a ∧
      (∃ extra, finalHeap = heap ++ extra) ∧ HeapRangeFold.Frame ["b", "c", "d", "e", "total", "best_sum", "best_set"] env afterEnv := by
  let invariant : Mutable.Heap → HeapCalls.Env → CliqueSearch.Best → Prop := fun heap env best =>
    ∃ _state : BestState heap env best, Prefix1 env a ∧ PrimeState heap env primeAddress primes
  have bindInvariant : ∀ heap env best b, invariant heap env best → b ∈ primes →
      invariant heap (setLocal env "b" (number b)) best := by
    intro heap env best b safe _
    rcases safe with ⟨state, values, input⟩
    exact ⟨state.bind "b" (number b) (by decide) (by decide), values.bind_b b, input.bind "b" (number b) (by decide)⟩
  have test : ∀ heap env best b, invariant heap env best → b ∈ primes → env "b" = some (number b) →
      Evaluates program env (guardFor "a" "b" ["a"]) heap (flag (acceptedB a b)) heap := by
    intro heap env best b safe _ getB
    rcases safe with ⟨state, values, input⟩
    exact guard_evaluates heap env "a" "b" ["a"] [a] a b values.getA getB
      (.cons values.getA (.nil))
  have cell : ∀ heap env best b, invariant heap env best → b ∈ primes → env "b" = some (number b) →
      ∃ afterEnv finalHeap, BlockContinues program env cLoopCode heap afterEnv finalHeap ∧
        invariant finalHeap afterEnv (primes.foldl (updateC primes a b) best) ∧
        (∃ extra, finalHeap = heap ++ extra) ∧ HeapRangeFold.Frame ["b", "c", "d", "e", "total", "best_sum", "best_set"] env afterEnv := by
    intro heap env best b safe _ getB
    rcases safe with ⟨state, values, input⟩
    obtain ⟨afterEnv, finalHeap, after, executed, finalValues, extra, frame⟩ :=
      c_loop_result heap env best state a b ⟨values.getA, getB⟩ primeAddress primes input
    refine ⟨afterEnv, finalHeap, executed, ⟨after, ⟨finalValues.getA⟩, input.after ["c", "d", "e", "total", "best_sum", "best_set"] extra frame (by simp)⟩, extra, ?_⟩
    intro name outside
    exact frame name (fun inside => outside (List.mem_cons_of_mem "b" inside))
  obtain ⟨afterEnv, finalHeap, executed, ⟨after, finalValues, _⟩, extra, frame⟩ :=
    HeapSequenceFold.for_guarded_list program "b" (guardFor "a" "b" ["a"]) cLoopCode rfl
      ["b", "c", "d", "e", "total", "best_sum", "best_set"] (by simp) (fun (b : Nat) => number b) (acceptedB a)
      (fun best b => primes.foldl (updateC primes a b) best)
      invariant primeAddress primes bindInvariant test cell heap env best ⟨state, values, input⟩
      (.name "primes") (by intros; simp) (Evaluates.lookup input.getPrimes) input.found
  exact ⟨afterEnv, finalHeap, after, by simpa only [bLoopCode_source, loopBody_b_source] using executed, finalValues, extra, frame⟩
def aLoopCode : List Stmt := (code.drop 3).take 1
theorem aLoopCode_source : aLoopCode = [.forIn (.name "a") (.name "primes") bLoopCode []] := rfl

def enumerationModel (primes : List Nat) (best : CliqueSearch.Best) : CliqueSearch.Best :=
  primes.foldl (fun best a => primes.foldl (updateB primes a) best) best

/-- The complete five nested source loops, with their shared local incumbent
and the full trial-division pair guards, compute the exhaustive fold model. -/
theorem enumeration_result (heap : Mutable.Heap) (env : HeapCalls.Env) (best : CliqueSearch.Best)
    (state : BestState heap env best) (primeAddress : Nat) (primes : List Nat)
    (input : PrimeState heap env primeAddress primes) :
    ∃ afterEnv finalHeap,
      ∃ _after : BestState finalHeap afterEnv (enumerationModel primes best),
      BlockContinues program env aLoopCode heap afterEnv finalHeap ∧ PrimeState finalHeap afterEnv primeAddress primes ∧
      (∃ extra, finalHeap = heap ++ extra) ∧
      HeapRangeFold.Frame ["a", "b", "c", "d", "e", "total", "best_sum", "best_set"] env afterEnv := by
  let invariant : Mutable.Heap → HeapCalls.Env → CliqueSearch.Best → Prop := fun heap env best =>
    ∃ _state : BestState heap env best, PrimeState heap env primeAddress primes
  have bindInvariant : ∀ heap env best a, invariant heap env best → a ∈ primes →
      invariant heap (setLocal env "a" (number a)) best := by
    intro heap env best a safe _
    rcases safe with ⟨state, input⟩
    exact ⟨state.bind "a" (number a) (by decide) (by decide), input.bind "a" (number a) (by decide)⟩
  have cell : ∀ heap env best a, invariant heap env best → a ∈ primes → env "a" = some (number a) →
      ∃ afterEnv finalHeap, BlockContinues program env bLoopCode heap afterEnv finalHeap ∧
        invariant finalHeap afterEnv (primes.foldl (updateB primes a) best) ∧
        (∃ extra, finalHeap = heap ++ extra) ∧
        HeapRangeFold.Frame ["a", "b", "c", "d", "e", "total", "best_sum", "best_set"] env afterEnv := by
    intro heap env best a safe _ getA
    rcases safe with ⟨state, input⟩
    obtain ⟨afterEnv, finalHeap, after, executed, _, extra, frame⟩ := b_loop_result heap env best state a ⟨getA⟩
      primeAddress primes input
    refine ⟨afterEnv, finalHeap, executed,
      ⟨after, input.after ["b", "c", "d", "e", "total", "best_sum", "best_set"] extra frame (by simp)⟩, extra, ?_⟩
    intro name outside
    exact frame name (fun inside => outside (List.mem_cons_of_mem "a" inside))
  obtain ⟨afterEnv, finalHeap, executed, ⟨after, finalInput⟩, extra, frame⟩ :=
    HeapSequenceFold.for_list program "a" bLoopCode rfl ["a", "b", "c", "d", "e", "total", "best_sum", "best_set"]
      (by simp) (fun (a : Nat) => number a) (fun best a => primes.foldl (updateB primes a) best)
      invariant primeAddress primes bindInvariant cell heap env best ⟨state, input⟩
      (.name "primes") (by intros; simp) (Evaluates.lookup input.getPrimes) input.found
  exact ⟨afterEnv, finalHeap, after, by simpa only [aLoopCode_source] using executed, finalInput, extra, frame⟩

def primeFilter : Expr := .boolOp .and
  [.compare (.name "p") [(.notEq, .constant (.int 5))], .call (.name "is_prime") [.name "p"]]
def keepPrime (p : Nat) : Bool := decide (p ≠ 5) && prime p
def vertices (limit : Int) : List Nat := (List.range' 3 (limit - 2).toNat).filter keepPrime
def primeExpression : Expr := .listComp (.name "p")
  [("p", .call (.name "range") [.constant (.int 3), .binOp (.name "limit") .add (.constant (.int 1))], [primeFilter])]
def primeBody (address : Nat) : List Stmt := [.ifThen primeFilter [.comprehensionAppend address (.name "p")] []]

theorem prime_filter_evaluates (heap : Mutable.Heap) (env : HeapCalls.Env) (p : Nat)
    (getP : env "p" = some (number p)) : Evaluates program env primeFilter heap (flag (keepPrime p)) heap := by
  have compared : Evaluates program env (.compare (.name "p") [(.notEq, .constant (.int 5))])
      heap (flag (decide (p ≠ 5))) heap :=
    Evaluates.compare (Evaluates.lookup getP) Evaluates.constant (by simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega)
  by_cases five : p = 5
  · subst p
    simpa only [keepPrime, ne_eq, not_true_eq_false, decide_false, Bool.false_and] using
      Evaluates.boolean_stop (op := .and) (flag := false) compared rfl rfl
  · have positive : decide (p ≠ 5) = true := by simp [five]
    simp only [keepPrime, positive, Bool.true_and]
    apply Evaluates.boolean_next (flag := true) (by simpa only [positive] using compared) rfl rfl
    exact Evaluates.boolean_last (flag := prime p)
      (Evaluates.call (.cons (Evaluates.lookup getP) .nil) (prime_heap_call p heap)) (by cases prime (p : Int) <;> rfl)

private theorem prime_filter_loop (base : Mutable.Heap) (first count stop : Nat) (endAt : first + count = stop)
    (before : List Nat) (env : HeapCalls.Env) :
    ∃ afterEnv, BlockContinues program env [.rangeStepLoop "p" first stop 1 (primeBody base.length) []]
      (HeapCollection.working base (numbers before) []) afterEnv
      (HeapCollection.working base (numbers (before ++ (List.range' first count).filter keepPrime)) []) := by
  induction count generalizing first before env with
  | zero =>
    refine ⟨env, ?_⟩
    simp only [List.range'_zero, List.filter_nil, List.append_nil]
    exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  | succ count ih =>
    let bound := setLocal env "p" (number first)
    have getP : bound "p" = some (number first) := by simp [bound, setLocal]
    have tested := prime_filter_evaluates (HeapCollection.working base (numbers before) []) bound first getP
    cases accepted : keepPrime first with
    | false =>
      have skipped : BlockContinues program bound (primeBody base.length)
          (HeapCollection.working base (numbers before) []) bound (HeapCollection.working base (numbers before) []) :=
        BlockContinues.branch (flag := false) (by simpa only [accepted] using tested) rfl .nil
      obtain ⟨afterEnv, continued⟩ := ih (first+1) (by omega) before bound
      refine ⟨afterEnv, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, primeBody,
        List.range'_succ, List.filter_cons, accepted] using skipped.append continued
    | true =>
      have emitted : BlockContinues program bound (primeBody base.length)
          (HeapCollection.working base (numbers before) []) bound
          (HeapCollection.working base (numbers (before ++ [first])) []) := by
        apply BlockContinues.branch (flag := true) (by simpa only [accepted] using tested) rfl
        simpa only [numbers, List.map_append, List.map_cons, List.map_nil, List.append_nil] using
          (HeapCollection.emit (program := program) base (numbers before) [] [] (number first)
            (by simpa only [List.append_nil] using
              (Evaluates.lookup (module := program) (heap := HeapCollection.working base (numbers before) []) getP)))
      obtain ⟨afterEnv, continued⟩ := ih (first+1) (by omega) (before ++ [first]) bound
      refine ⟨afterEnv, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, primeBody,
        List.range'_succ, List.filter_cons, accepted, List.append_assoc] using emitted.append continued

theorem primes_evaluate (heap : Mutable.Heap) (env : HeapCalls.Env) (limit : Int)
    (getLimit : env "limit" = some (number limit)) :
    Evaluates program env primeExpression heap (.ref heap.length) (heap ++ [.list (numbers (vertices limit))]) := by
  let generators : List (String × Expr × List Expr) := [("p", .call (.name "range")
    [.constant (.int 3), .binOp (.name "limit") .add (.constant (.int 1))], [primeFilter])]
  let masked := comprehensionEnv env generators
  have arguments : Evaluates.Arguments program env
      [.constant (.int 3), .binOp (.name "limit") .add (.constant (.int 1))]
      heap [number 3, number (limit+1)] heap :=
    .cons Evaluates.constant (.cons (Evaluates.binary (Evaluates.lookup getLimit) Evaluates.constant rfl) .nil)
  by_cases small : limit < 3
  · have empty : vertices limit = [] := by
      have count : (limit-2).toNat = 0 := by omega
      simp [vertices, count]
    rw [empty]
    apply Evaluates.list_comp_range (finalEnv := masked) arguments rfl
    exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  · obtain ⟨afterEnv, executed⟩ := prime_filter_loop heap 3 (limit-2).toNat (3+(limit-2).toNat) rfl [] masked
    have castBound : ((3+(limit-2).toNat : Nat) : Int) = limit+1 := by omega
    rw [castBound] at executed
    apply Evaluates.list_comp_range (finalEnv := afterEnv) arguments rfl
    simpa only [masked, generators, comprehensionFilters, comprehensionBody, primeBody, HeapCollection.working,
      List.nil_append, vertices] using executed

def sentinel : Int := 10 ^ 30
def setupCode : List Stmt := code.take 3
theorem setupCode_source : setupCode =
    [.assign [.name "primes"] primeExpression,
     .assign [.name "best_sum"] (.binOp (.constant (.int 10)) .pow (.constant (.int 30))),
     .annAssign (.name "best_set") (.subscript (.name "list") (.name "int")) (some (.list []))] := rfl
def setupHeap (heap : Mutable.Heap) (limit : Int) : Mutable.Heap :=
  heap ++ [.list (numbers (vertices limit)), .list []]
def setupEnv (env : HeapCalls.Env) (heap : Mutable.Heap) : HeapCalls.Env :=
  setLocal (setLocal (setLocal env "primes" (.ref heap.length)) "best_sum" (number sentinel))
    "best_set" (.ref (heap.length+1))

theorem setup_result (heap : Mutable.Heap) (env : HeapCalls.Env) (limit : Int)
    (getLimit : env "limit" = some (number limit)) :
    BlockContinues program env setupCode heap (setupEnv env heap) (setupHeap heap limit) := by
  let primed := setLocal env "primes" (.ref heap.length)
  let bounded := setLocal primed "best_sum" (number sentinel)
  have first : BlockContinues program env [setupCode[0]'(by decide)] heap primed
      (heap ++ [.list (numbers (vertices limit))]) :=
    BlockContinues.assign (primes_evaluate heap env limit getLimit)
  have second : BlockContinues program primed [setupCode[1]'(by decide)]
      (heap ++ [.list (numbers (vertices limit))]) bounded (heap ++ [.list (numbers (vertices limit))]) :=
    BlockContinues.assign (Evaluates.binary Evaluates.constant Evaluates.constant rfl)
  have third : BlockContinues program bounded [setupCode[2]'(by decide)]
      (heap ++ [.list (numbers (vertices limit))]) (setupEnv env heap) (setupHeap heap limit) := by
    apply BlockContinues.annAssign
    convert (Evaluates.list (module := program) (env := bounded)
      (heap := heap ++ [.list (numbers (vertices limit))]) .nil) using 1 <;>
      simp [setupHeap, List.append_assoc]
  simpa only [setupCode_source] using first.append (second.append third)

def initialState (heap : Mutable.Heap) (env : HeapCalls.Env) (limit : Int) :
    BestState (setupHeap heap limit) (setupEnv env heap) ⟨sentinel, []⟩ where
  selectedAddress := heap.length+1
  getSum := by simp [setupEnv, setLocal]
  getSet := by simp [setupEnv, setLocal]
  found := by simp [setupHeap, numbers]

def initialPrimes (heap : Mutable.Heap) (env : HeapCalls.Env) (limit : Int) :
    PrimeState (setupHeap heap limit) (setupEnv env heap) heap.length (vertices limit) where
  getPrimes := by simp [setupEnv, setLocal]
  found := by simp [setupHeap]

def returnExpression : Expr := .tuple [.name "best_sum", .name "best_set"]
theorem code_source : code = setupCode ++ aLoopCode ++ [.return returnExpression] := rfl
def answerModel (limit : Int) : CliqueSearch.Best := enumerationModel (vertices limit) ⟨sentinel, []⟩

/-- The complete exhaustive reference source, including signed range bounds,
trial-division filtering, all five nested loops, and the final result tuple. -/
theorem result (limit : Int) (caller : Mutable.Heap) :
    ∃ finalHeap selectedAddress,
      ReturnsValue program "naive" [number limit] caller (.ref finalHeap.length)
        (finalHeap ++ [.tuple [number (answerModel limit).bound, .ref selectedAddress]]) ∧
      finalHeap[selectedAddress]? = some (.list (numbers (answerModel limit).chosen)) ∧
      (∃ extra, finalHeap = caller ++ extra) := by
  let params := ((findFunctionIn program.body "naive").getD ([], [])).1
  let sourceBody := ((findFunctionIn program.body "naive").getD ([], [])).2
  let env := functionEnv params sourceBody [number limit] []
  have getLimit : env "limit" = some (number limit) := rfl
  have initialized := setup_result caller env limit getLimit
  obtain ⟨afterEnv, finalHeap, after, enumerated, _, extra, _⟩ := enumeration_result (setupHeap caller limit)
    (setupEnv env caller) ⟨sentinel, []⟩ (initialState caller env limit) caller.length (vertices limit)
    (initialPrimes caller env limit)
  refine ⟨finalHeap, after.selectedAddress, ?_, after.found, ?_⟩
  · apply BlockReturns.function rfl rfl
    change BlockReturns program env code caller (.ref finalHeap.length)
      (finalHeap ++ [.tuple [number (answerModel limit).bound, .ref after.selectedAddress]])
    rw [code_source]
    exact (initialized.append enumerated).returns (BlockReturns.return_value
      (Evaluates.tuple (.cons (Evaluates.lookup after.getSum) (.cons (Evaluates.lookup after.getSet) .nil)) (by simp)))
  · obtain ⟨extra, same⟩ := extra
    exact ⟨[.list (numbers (vertices limit)), .list []] ++ extra, by rw [same, setupHeap, List.append_assoc]⟩

theorem «Returns» (limit : Int) : (HeapCalls.call program "naive" [number limit] []).Returns := by
  obtain ⟨_, _, returned, _, _⟩ := result limit []
  exact returned.returns

theorem «Supported» (limit : Int) : (HeapCalls.call program "naive" [number limit] []).Supported :=
  («Returns» limit).supported

end data.«project-euler-statements».data.py.project_euler_statements.p60.naive
