import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p46.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.TruthCalls
import ProjectEulerSolutions.Lib.PrimeTwiceSquareSuccessor
import lang.py.FormalSW.LoopProgress
import lang.py.FormalSW.Linking

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p46
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.PrimeTwiceSquare
private abbrev program := P46Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev natural (n : Nat) : Mutable.Value := number n
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 5 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["is_odd_composite", "can_be_written", "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem prime_result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "is_prime" [natural n] heap (flag (decide (Nat.Prime n))) heap :=
  (common.is_prime.heap_result n heap).extend common_extension

namespace is_odd_composite
/-- The three source tests short-circuit without modifying the caller's heap. -/
theorem result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "is_odd_composite" [natural n] heap (flag (oddComposite n)) heap := by
  let initial := functionEnv ((findFunctionIn program.body "is_odd_composite").getD ([], [])).1
    ((findFunctionIn program.body "is_odd_composite").getD ([], [])).2 [natural n] []
  have parity : Evaluates program initial
      (.compare (.binOp (.name "n") .mod (.constant (.int 2))) [(.eq, .constant (.int 1))])
      heap (flag (decide (n%2=1))) heap := by
    apply Evaluates.compare (av := natural (n%2)) (bv := natural 1) (middle := heap) (afterRight := heap)
    · exact Evaluates.binary (av := natural n) (bv := natural 2)
        (Evaluates.lookup rfl) Evaluates.constant (by simp [Mutable.binary, scalarBinary])
    · exact Evaluates.constant
    · change some (Except.ok (ε := ExceptionObject) (flag (decide (((n%2 : Nat) : Int)=((1 : Nat) : Int)))), heap)=_
      simp only [Int.natCast_inj]
  have composite : Evaluates program initial (.unaryOp .not (.call (.name "is_prime") [.name "n"]))
      heap (flag (!decide (Nat.Prime n))) heap := by
    apply Evaluates.unary
      (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (prime_result n heap))
    rfl
  have large : Evaluates program initial (.compare (.name "n") [(.gt, .constant (.int 1))])
      heap (flag (decide (1<n))) heap := by
    apply Evaluates.compare (av := natural n) (bv := natural 1) (middle := heap) (afterRight := heap)
      (Evaluates.lookup rfl) Evaluates.constant
    change some (Except.ok (ε := ExceptionObject) (flag (decide (((1 : Nat) : Int)<(n : Int)))), heap)=_
    simp only [Int.ofNat_lt]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  by_cases odd : n%2=1
  · apply Evaluates.boolean_next (flag := true) (by simpa only [odd, decide_true] using parity) rfl rfl
    by_cases prime : Nat.Prime n
    · simp only [oddComposite, prime, not_true_eq_false, and_false, false_and, decide_false]
      exact Evaluates.boolean_stop (flag := false) (by simpa only [prime, decide_true, Bool.not_true] using composite) rfl rfl
    · apply Evaluates.boolean_next (flag := true) (by simpa only [prime, decide_false, Bool.not_false] using composite) rfl rfl
      apply Evaluates.boolean_last (truth := rfl)
      simpa only [oddComposite, odd, prime, not_false_eq_true, true_and] using large
  · simp only [oddComposite, odd, false_and, decide_false]
    exact Evaluates.boolean_stop (flag := false) (by simpa only [odd, decide_false] using parity) rfl rfl
end is_odd_composite

private abbrev scalarNumber (n : Int) : Constant := .int n
private abbrev scalarNatural (n : Nat) : Constant := scalarNumber n
private abbrev scalarFlag (b : Bool) : Constant := .bool b

private theorem scalar_prime (n : Nat) :
    Calls.ReturnsValue program "is_prime" [scalarNatural n] (scalarFlag (decide (Nat.Prime n))) :=
  (common.is_prime.result n).extend common_extension.toExtends

namespace is_odd_composite

theorem scalar_result (n : Nat) :
    Calls.ReturnsValue program "is_odd_composite" [scalarNatural n] (scalarFlag (oddComposite n)) := by
  let initial := argumentEnv ((findFunctionIn program.body "is_odd_composite").getD ([], [])).1 [scalarNatural n]
  have parity : Calls.Evaluates program initial
      (.compare (.binOp (.name "n") .mod (.constant (.int 2))) [(.eq, .constant (.int 1))])
      (scalarFlag (decide (n % 2 = 1))) :=
    Calls.Evaluates.compare (av := scalarNatural (n % 2)) (bv := scalarNatural 1)
      (Calls.Evaluates.binary (av := scalarNatural n) (bv := scalarNatural 2)
        (Calls.Evaluates.lookup rfl) Calls.Evaluates.constant (by simp [scalarBinary]))
      Calls.Evaluates.constant (by
        change some (decide (((n % 2 : Nat) : Int) = ((1 : Nat) : Int))) = _
        simp only [Int.natCast_inj])
  have composite : Calls.Evaluates program initial (.unaryOp .not (.call (.name "is_prime") [.name "n"]))
      (scalarFlag (!decide (Nat.Prime n))) :=
    Calls.Evaluates.unary (Calls.Evaluates.call (.cons (Calls.Evaluates.lookup rfl) .nil) (scalar_prime n)) rfl
  have large : Calls.Evaluates program initial (.compare (.name "n") [(.gt, .constant (.int 1))])
      (scalarFlag (decide (1 < n))) :=
    Calls.Evaluates.compare (Calls.Evaluates.lookup rfl) Calls.Evaluates.constant (by simp [scalarCompare, evalCmpOp])
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  by_cases odd : n % 2 = 1
  · apply Calls.Evaluates.boolean_continue (by simpa only [odd, decide_true] using parity) rfl
    by_cases prime : Nat.Prime n
    · simp only [oddComposite, prime, not_true_eq_false, and_false, false_and, decide_false]
      exact Calls.Evaluates.boolean_stop (by simpa only [prime, decide_true, Bool.not_true] using composite) rfl
    · apply Calls.Evaluates.boolean_continue (by simpa only [prime, decide_false, Bool.not_false] using composite) rfl
      apply Calls.Evaluates.boolean_last
      simpa only [oddComposite, odd, prime, not_false_eq_true, true_and] using large
  · simp only [oddComposite, odd, false_and, decide_false]
    exact Calls.Evaluates.boolean_stop (by simpa only [odd, decide_false] using parity) rfl

end is_odd_composite

namespace can_be_written
open ProjectEulerSolutions.PrimeTwiceSquareSuccessor
private def squareExpression : Expr := .binOp (.binOp (.constant (.int 2)) .mult (.name "k")) .mult (.name "k")
private def condition : Expr := .compare squareExpression [(.lt, .name "n")]
private def primeExpression : Expr := .call (.name "is_prime") [.binOp (.name "n") .sub squareExpression]
private def body : List Stmt :=
  [.ifThen primeExpression [.return (.constant (.bool true))] [], .augAssign (.name "k") .add (.constant (.int 1))]
private def searchLoop : Stmt := .whileDo condition body []

private theorem square_evaluate (k : Nat) (env : ScalarEnv) (getK : env "k" = some (scalarNatural k)) :
    Calls.Evaluates program env squareExpression (scalarNatural (2 * k * k)) := by
  exact Calls.Evaluates.binary (av := scalarNatural (2 * k)) (bv := scalarNatural k)
    (Calls.Evaluates.binary Calls.Evaluates.constant (Calls.Evaluates.lookup getK) (by simp [scalarBinary]))
    (Calls.Evaluates.lookup getK) (by simp [scalarBinary])

private theorem condition_evaluate (n : Int) (k : Nat) (env : ScalarEnv)
    (getN : env "n" = some (scalarNumber n)) (getK : env "k" = some (scalarNatural k)) :
    Calls.Evaluates program env condition (scalarFlag (decide (((2 * k * k : Nat) : Int) < n))) :=
  Calls.Evaluates.compare (square_evaluate k env getK) (Calls.Evaluates.lookup getN) (by simp [scalarCompare, evalCmpOp])

/-- Each supported square trial either returns a witness or decreases the distance to the input. -/
private theorem loop (n k : Nat) (positive : 0 < k) (env : ScalarEnv)
    (getN : env "n" = some (scalarNatural n)) (getK : env "k" = some (scalarNatural k)) :
    Calls.BlockReturns program env [searchLoop, .return (.constant (.bool false))] (scalarFlag (tailWritten n k)) := by
  have tested : Calls.Evaluates program env condition (scalarFlag (decide (2 * k * k < n))) := by
    simpa only [Int.ofNat_lt] using condition_evaluate n k env getN getK
  by_cases small : 2 * k * k < n
  · have subtract : ((n - 2 * k * k : Nat) : Int) = (n : Int) - (2 * k * k : Nat) := by omega
    have primeTest : Calls.Evaluates program env primeExpression (scalarFlag (decide (Nat.Prime (n - 2 * k * k)))) := by
      apply Calls.Evaluates.call (values := [scalarNatural (n - 2 * k * k)])
      · refine .cons ?_ .nil
        exact Calls.Evaluates.binary (Calls.Evaluates.lookup getN) (square_evaluate k env getK)
          (by simp [scalarBinary, subtract])
      · exact scalar_prime _
    by_cases prime : Nat.Prime (n - 2 * k * k)
    · rw [tail_current n k small prime]
      rw [decide_eq_true small] at tested
      rw [decide_eq_true prime] at primeTest
      apply Calls.BlockReturns.while_loop tested
      apply Calls.BlockReturns.branch primeTest
      exact Calls.BlockReturns.return_value Calls.Evaluates.constant
    · rw [tail_next n k prime]
      have before : k < n := by nlinarith [Nat.le_mul_self k]
      have rest := loop n (k + 1) (by omega) (env.set "k" (scalarNatural (k + 1)))
        (by simpa [ScalarEnv.set] using getN) (by simp [ScalarEnv.set])
      rw [decide_eq_true small] at tested
      rw [decide_eq_false prime] at primeTest
      apply Calls.BlockReturns.while_loop tested
      apply Calls.BlockReturns.branch primeTest
      apply Calls.BlockReturns.augAssign (value := scalarNatural (k + 1))
        (Calls.Evaluates.binary (Calls.Evaluates.lookup getK) Calls.Evaluates.constant (by simp [scalarBinary]))
      simpa only [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        Bool.false_or, Bool.false_eq_true, if_false, List.nil_append] using rest
  · rw [tail_stopped n k (by omega)]
    rw [decide_eq_false small] at tested
    apply Calls.BlockReturns.while_loop tested
    exact Calls.BlockReturns.return_value Calls.Evaluates.constant
termination_by n - k
decreasing_by omega

def written (n : Int) : Bool := if n < 0 then false else fast n.toNat

/-- The unbounded square scan terminates with the exact representation predicate for every signed input. -/
theorem result (n : Int) : Calls.ReturnsValue program "can_be_written" [scalarNumber n] (scalarFlag (written n)) := by
  let initial := argumentEnv ((findFunctionIn program.body "can_be_written").getD ([], [])).1 [scalarNumber n]
  let ready := initial.set "k" (scalarNatural 1)
  by_cases negative : n < 0
  · simp only [written, if_pos negative]
    have tested := condition_evaluate n 1 ready (by simp [ready, initial, ScalarEnv.set]; rfl) (by simp [ready, ScalarEnv.set])
    have stopped : ¬ (((2 * 1 * 1 : Nat) : Int) < n) := by omega
    rw [decide_eq_false stopped] at tested
    apply Calls.BlockReturns.function rfl rfl
    apply Calls.BlockReturns.assign Calls.Evaluates.constant
    apply Calls.BlockReturns.while_loop tested
    exact Calls.BlockReturns.return_value Calls.Evaluates.constant
  · lift n to Nat using (by omega : 0 ≤ n)
    simp only [written, if_neg (by omega : ¬ (n : Int) < 0), Int.toNat_natCast]
    rw [← tail_start]
    apply Calls.BlockReturns.function rfl rfl
    apply Calls.BlockReturns.assign Calls.Evaluates.constant
    exact loop n 1 (by decide) ready (by simp [ready, initial, ScalarEnv.set]; rfl) (by simp [ready, ScalarEnv.set])

theorem «Returns» (n : Int) : (Calls.function program "can_be_written" [.int n]).Returns := (result n).returns

end can_be_written


namespace naive
open ProjectEulerSolutions.PrimeTwiceSquareSuccessor
private def predicate : Expr := .boolOp .and
  [.compare (.name "n") [(.gt, .name "after")], .call (.name "is_odd_composite") [.name "n"],
    .unaryOp .not (.call (.name "can_be_written") [.name "n"])]
private def body : List Stmt :=
  [.ifThen predicate [.return (.name "n")] [], .augAssign (.name "n") .add (.constant (.int 2))]
private def searchLoop : Stmt := .whileDo (.constant (.bool true)) body []

private theorem tested (after : Int) (index : Nat) (env : ScalarEnv)
    (getAfter : env "after" = some (scalarNumber after)) (getN : env "n" = some (scalarNatural (value index))) :
    Calls.Evaluates program env predicate (scalarFlag (accepts after (value index))) := by
  have later : Calls.Evaluates program env (.compare (.name "n") [(.gt, .name "after")])
      (scalarFlag (decide (after < (value index : Int)))) :=
    Calls.Evaluates.compare (Calls.Evaluates.lookup getN) (Calls.Evaluates.lookup getAfter) (by simp [scalarCompare, evalCmpOp])
  have composite : Calls.Evaluates program env (.call (.name "is_odd_composite") [.name "n"])
      (scalarFlag (oddComposite (value index))) :=
    Calls.Evaluates.call (.cons (Calls.Evaluates.lookup getN) .nil) (is_odd_composite.scalar_result _)
  have written : Calls.Evaluates program env (.unaryOp .not (.call (.name "can_be_written") [.name "n"]))
      (scalarFlag (!fast (value index))) := by
    apply Calls.Evaluates.unary
    · apply Calls.Evaluates.call (.cons (Calls.Evaluates.lookup getN) .nil)
      simpa only [can_be_written.written, if_neg (show ¬ (value index : Int) < 0 by omega), Int.toNat_natCast] using
        can_be_written.result (value index)
    · rfl
  by_cases above : after < (value index : Int)
  · simp only [accepts, above, decide_true, Bool.true_and, counterexample]
    apply Calls.Evaluates.boolean_continue (by simpa only [above, decide_true] using later) rfl
    cases current : oddComposite (value index) with
    | false =>
        simp only [Bool.false_and]
        exact Calls.Evaluates.boolean_stop (by simpa only [current] using composite) rfl
    | true =>
        simp only [Bool.true_and]
        apply Calls.Evaluates.boolean_continue (by simpa only [current] using composite) rfl
        exact Calls.Evaluates.boolean_last written
  · simp only [accepts, above, decide_false, Bool.false_and]
    exact Calls.Evaluates.boolean_stop (by simpa only [above, decide_false] using later) rfl

/-- A rejected candidate advances normally; no finite outer bound is used. -/
private theorem advance (after : Int) (index : Nat) (rejected : accepts after (value index) = false)
    (env : ScalarEnv) (getAfter : env "after" = some (scalarNumber after))
    (getN : env "n" = some (scalarNatural (value index))) :
    Calls.BlockContinues program env body (env.set "n" (scalarNatural (value (index + 1)))) := by
  have evaluated := tested after index env getAfter getN
  rw [rejected] at evaluated
  have skipped : Calls.BlockContinues program env [body[0]'(by decide)] env :=
    Calls.BlockContinues.branch evaluated Calls.BlockContinues.nil
  have incremented : Calls.BlockContinues program env [body[1]'(by decide)]
      (env.set "n" (scalarNatural (value (index + 1)))) := by
    apply Calls.BlockContinues.augAssign
    exact Calls.Evaluates.binary (Calls.Evaluates.lookup getN) Calls.Evaluates.constant
      (by simp [scalarBinary, value, Nat.mul_add, Int.add_assoc])
  exact skipped.append incremented

private theorem loop (after : Int) (success : Success after) (index : Nat) (bounded : index ≤ winnerIndex after success)
    (env : ScalarEnv) (getAfter : env "after" = some (scalarNumber after))
    (getN : env "n" = some (scalarNatural (value index))) :
    Calls.BlockReturns program env [searchLoop] (scalarNatural (answer after success)) := by
  by_cases same : index = winnerIndex after success
  · have evaluated := tested after index env getAfter getN
    have accepted : accepts after (value index) = true := by simpa only [same, answer] using winner_accepted after success
    rw [accepted] at evaluated
    apply Calls.BlockReturns.while_loop (value := .bool true) Calls.Evaluates.constant
    apply Calls.BlockReturns.branch evaluated
    apply Calls.BlockReturns.return_value
    exact Calls.Evaluates.lookup (by simpa only [same, answer] using getN)
  · have before : index < winnerIndex after success := by omega
    have advanced := advance after index (earlier_rejected after success index before) env getAfter getN
    have returned := loop after success (index + 1) (by omega) (env.set "n" (scalarNatural (value (index + 1))))
      (by simpa [ScalarEnv.set] using getAfter) (by simp [ScalarEnv.set])
    apply Calls.BlockReturns.while_loop (value := .bool true) Calls.Evaluates.constant
    simpa only [Calls.loopContinuation, show Calls.loopControl body = false from rfl, Bool.false_eq_true, if_false] using
      advanced.returns returned
termination_by winnerIndex after success - index
decreasing_by omega

/-- A mathematical counterexample witness executes the complete unbounded reference search. -/
theorem result (after : Int) (success : Success after) :
    Calls.ReturnsValue program "naive" [scalarNumber after] (scalarNatural (answer after success)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.assign Calls.Evaluates.constant
  exact loop after success 0 (by omega) _ rfl rfl

/-- Without a counterexample above the threshold, every reference iteration remains supported. -/
theorem diverges (after : Int) (absent : ¬ Success after) :
    (Calls.function program "naive" [.int after]).Diverges := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let sourceBody := ((findFunctionIn program.body "naive").getD ([], [])).2
  let entry := argumentEnv args [scalarNumber after]
  let initial := entry.set "n" (scalarNatural 9)
  let invariant : ScalarEnv → Prop := fun env =>
    ∃ index : Nat, env "after" = some (scalarNumber after) ∧ env "n" = some (scalarNatural (value index))
  apply Calls.scalar_while_diverges program "naive" [.int after] args sourceBody
    [.assign [.name "n"] (.constant (.int 9))] body rfl rfl rfl rfl invariant initial
  · exact Calls.BlockContinues.assign Calls.Evaluates.constant
  · exact ⟨0, by simp [initial, entry, ScalarEnv.set]; rfl, by simp [initial, ScalarEnv.set, value]⟩
  · intro env current
    obtain ⟨index, getAfter, getN⟩ := current
    refine ⟨env.set "n" (scalarNatural (value (index + 1))), advance after index (no_success after absent index) env getAfter getN,
      index + 1, ?_, ?_⟩
    · simpa [ScalarEnv.set] using getAfter
    · simp [ScalarEnv.set]

end naive

end data.«project-euler-statements».data.py.project_euler_statements.p46
