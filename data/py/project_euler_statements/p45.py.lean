import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p45.py.ast»
import lang.py.FormalSW.TruthCalls
import lang.py.FormalSW.ScalarComparisons
import ProjectEulerSolutions.Lib.TriPentHex
import ProjectEulerSolutions.Lib.TriPentHexUnbounded

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p45
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.TriPentHex
private abbrev program := P45Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev natural (n : Nat) : Mutable.Value := number n
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)

def triPolynomial (n : Int) : Int := n*(n+1)/2
def pentPolynomial (n : Int) : Int := n*(3*n-1)/2
def hexPolynomial (n : Int) : Int := n*(2*n-1)

theorem tri_nat (n : Nat) : triPolynomial n=(triangular n : Int) := by
  simp [triPolynomial, triangular]

theorem pent_nat (n : Nat) : pentPolynomial n=(pentagonal n : Int) := by
  cases n with
  | zero => rfl
  | succ n => simp [pentPolynomial, pentagonal, ProjectEulerSolutions.PentagonalDiscriminant.pentagonal,
      Int.natCast_sub (show 1 ≤ 3*(n+1) by omega)]

theorem hex_nat (n : Nat) : hexPolynomial n=(hexagonal n : Int) := by
  cases n with
  | zero => rfl
  | succ n => simp [hexPolynomial, hexagonal, Int.natCast_sub (show 1 ≤ 2*(n+1) by omega)]

namespace tri
theorem result (n : Int) (heap : Mutable.Heap) :
    ReturnsValue program "tri" [number n] heap (number (triPolynomial n)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := number (n*(n+1))) (bv := number 2) (middle := heap) (afterRight := heap)
  · exact Evaluates.binary (av := number n) (bv := number (n+1)) (middle := heap) (afterRight := heap)
      (Evaluates.lookup rfl) (Evaluates.binary (av := number n) (bv := number 1) (middle := heap) (afterRight := heap)
        (Evaluates.lookup rfl) Evaluates.constant rfl) rfl
  · exact Evaluates.constant
  · rfl
end tri

namespace pent
theorem result (n : Int) (heap : Mutable.Heap) :
    ReturnsValue program "pent" [number n] heap (number (pentPolynomial n)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := number (n*(3*n-1))) (bv := number 2) (middle := heap) (afterRight := heap)
  · apply Evaluates.binary (av := number n) (bv := number (3*n-1)) (middle := heap) (afterRight := heap) (Evaluates.lookup rfl)
    · exact Evaluates.binary (av := number (3*n)) (bv := number 1) (middle := heap) (afterRight := heap)
        (Evaluates.binary (av := number 3) (bv := number n) (middle := heap) (afterRight := heap)
          Evaluates.constant (Evaluates.lookup rfl) rfl) Evaluates.constant rfl
    · rfl
  · exact Evaluates.constant
  · rfl
end pent

namespace hex
theorem result (n : Int) (heap : Mutable.Heap) :
    ReturnsValue program "hex" [number n] heap (number (hexPolynomial n)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := number n) (bv := number (2*n-1)) (middle := heap) (afterRight := heap) (Evaluates.lookup rfl)
  · exact Evaluates.binary (av := number (2*n)) (bv := number 1) (middle := heap) (afterRight := heap)
      (Evaluates.binary (av := number 2) (bv := number n) (middle := heap) (afterRight := heap)
        Evaluates.constant (Evaluates.lookup rfl) rfl) Evaluates.constant rfl
  · rfl
end hex

private def membership (value : Nat → Nat) (x : Int) : Bool :=
  if x < 0 then false else (List.range (x.toNat+1)).any fun n => decide (value n=x.toNat)

def pentTest (x : Int) : Bool := membership pentagonal x
def hexValueTest (x : Int) : Bool := membership hexagonal x

private def membershipCondition (name : String) : Expr :=
  .compare (.call (.name name) [.name "n"]) [(.eq, .name "x")]

private theorem membership_loop (name : String) (value : Nat → Nat)
    (callback : ∀ (n : Nat) (heap : Mutable.Heap), ReturnsValue program name [natural n] heap (natural (value n)) heap)
    (x first count stop : Nat) (equation : first+count=stop) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getX : env "x" = some (natural x)) :
    BlockReturns program env [.rangeStepLoop "n" first stop 1 (truthBody false (membershipCondition name)) [],
      .return (.constant (.bool false))] heap
      (flag ((List.range' first count).any fun n => decide (value n=x))) heap := by
  induction count generalizing first env with
  | zero =>
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value Evaluates.constant
  | succ count ih =>
      let bound := setLocal env "n" (natural first)
      have tested : Evaluates program bound (membershipCondition name) heap (flag (decide (value first=x))) heap := by
        apply Evaluates.compare (av := natural (value first)) (bv := natural x) (middle := heap) (afterRight := heap)
          (Evaluates.call (values := [natural first]) (.cons (Evaluates.lookup (by simp [bound, setLocal])) .nil) (callback first heap))
          (Evaluates.lookup (by simpa [bound, setLocal] using getX))
        simp [HeapCalls.compare, scalarCompare, evalCmpOp]
      rw [List.range'_succ, List.any_cons]
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      by_cases found : value first=x
      · simp only [found, decide_true, Bool.true_or]
        apply BlockReturns.branch (flag := true) tested (by simp [Mutable.truth, scalarTruth, found])
        exact BlockReturns.return_value Evaluates.constant
      · simp only [found, decide_false, Bool.false_or]
        apply BlockReturns.branch (flag := false) tested (by simp [Mutable.truth, scalarTruth, found])
        have rest := ih (first+1) (by omega) bound (by simpa [bound, setLocal] using getX)
        simpa only [truthBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Bool.false_or, Bool.false_eq_true, if_false, List.nil_append, Int.natCast_add, Int.natCast_one] using rest

private theorem membership_evaluation (name : String) (value : Nat → Nat)
    (callback : ∀ (n : Nat) (heap : Mutable.Heap), ReturnsValue program name [natural n] heap (natural (value n)) heap)
    (x : Int) (heap : Mutable.Heap) (env : HeapCalls.Env) (getX : env "x" = some (number x)) :
    Evaluates program env
      (.consumeGenerator (.builtinCall .any []) (membershipCondition name)
        [(.name "n", .call (.name "range") [.binOp (.name "x") .add (.constant (.int 1))], [])])
      heap (flag (membership value x)) heap := by
  apply Evaluates.truth_generator_range (universal := false) (values := [number (x+1)])
    (.cons (Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup getX) Evaluates.constant rfl) .nil) rfl
  by_cases negative : x < 0
  · apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    simpa only [membership, if_pos negative] using
      (BlockReturns.return_value (module := program) (heap := heap) (env := _) (Evaluates.constant (value := .bool false)))
  · lift x to Nat using (by omega : 0 ≤ x)
    let inner := comprehensionTargetsEnv env
      [(.name "n", .call (.name "range") [.binOp (.name "x") .add (.constant (.int 1))], [])]
    have executed := membership_loop name value callback x 0 (x+1) (x+1) (by omega) heap inner
      (by simpa [inner, comprehensionTargetsEnv, targetLocals] using getX)
    simpa only [membership, if_neg (by omega : ¬ (x : Int)<0), Int.toNat_natCast,
      List.range_eq_range', Int.natCast_add, Int.natCast_one] using executed

namespace is_pent
/-- The brute-force pentagonal predicate terminates for every integer, including zero and negatives. -/
theorem result (x : Int) (heap : Mutable.Heap) :
    ReturnsValue program "is_pent" [number x] heap (flag (pentTest x)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact membership_evaluation "pent" pentagonal
    (fun n heap => by simpa only [pent_nat] using pent.result (n : Int) heap) x heap _ rfl

theorem «Returns» (x : Int) : (HeapCalls.scalarFunction program "is_pent" [.int x]).Returns :=
  (result x []).scalar_returns

theorem «Supported» (x : Int) : (HeapCalls.scalarFunction program "is_pent" [.int x]).Supported :=
  («Returns» x).supported
end is_pent

namespace is_hex
/-- The brute-force hexagonal predicate shares the same source loop, with a distinct polynomial callback. -/
theorem result (x : Int) (heap : Mutable.Heap) :
    ReturnsValue program "is_hex" [number x] heap (flag (hexValueTest x)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact membership_evaluation "hex" hexagonal
    (fun n heap => by simpa only [hex_nat] using hex.result (n : Int) heap) x heap _ rfl

theorem «Returns» (x : Int) : (HeapCalls.scalarFunction program "is_hex" [.int x]).Returns :=
  (result x []).scalar_returns

theorem «Supported» (x : Int) : (HeapCalls.scalarFunction program "is_hex" [.int x]).Supported :=
  («Returns» x).supported
end is_hex


namespace naive
open ProjectEulerSolutions.TriPentHexUnbounded
private abbrev scalarNumber (n : Int) : Constant := .int n
private abbrev scalarNatural (n : Nat) : Constant := scalarNumber n
private abbrev scalarFlag (b : Bool) : Constant := .bool b

private theorem scalar_tri (n : Int) : Calls.ReturnsValue program "tri" [scalarNumber n] (scalarNumber (triPolynomial n)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  exact Calls.Evaluates.binary
    (Calls.Evaluates.binary (Calls.Evaluates.lookup rfl)
      (Calls.Evaluates.binary (Calls.Evaluates.lookup rfl) Calls.Evaluates.constant rfl) rfl)
    Calls.Evaluates.constant rfl

private theorem scalar_pent (n : Int) : Calls.ReturnsValue program "pent" [scalarNumber n] (scalarNumber (pentPolynomial n)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  apply Calls.Evaluates.binary (av := scalarNumber (n * (3 * n - 1))) (bv := scalarNumber 2)
  · apply Calls.Evaluates.binary (av := scalarNumber n) (bv := scalarNumber (3 * n - 1)) (Calls.Evaluates.lookup rfl)
    · exact Calls.Evaluates.binary
        (Calls.Evaluates.binary Calls.Evaluates.constant (Calls.Evaluates.lookup rfl) rfl) Calls.Evaluates.constant rfl
    · rfl
  · exact Calls.Evaluates.constant
  · rfl

private theorem scalar_hex (n : Int) : Calls.ReturnsValue program "hex" [scalarNumber n] (scalarNumber (hexPolynomial n)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.return_value
  apply Calls.Evaluates.binary (av := scalarNumber n) (bv := scalarNumber (2 * n - 1)) (Calls.Evaluates.lookup rfl)
  · exact Calls.Evaluates.binary
      (Calls.Evaluates.binary Calls.Evaluates.constant (Calls.Evaluates.lookup rfl) rfl) Calls.Evaluates.constant rfl
  · rfl

private def values (i j k : Nat) : List Constant :=
  [scalarNatural (triangular i), scalarNatural (pentagonal j), scalarNatural (hexagonal k)]
private def prepared (env : ScalarEnv) (i j k : Nat) : ScalarEnv :=
  Calls.assignNames env ["t", "p", "h"] (values i j k)
private def foundTest : Expr := .boolOp .and
  [.compare (.name "t") [(.eq, .name "p"), (.eq, .name "h")],
    .compare (.name "t") [(.gt, .name "after")]]
private def firstTest : Expr := .boolOp .and
  [.compare (.name "t") [(.ltE, .name "p")], .compare (.name "t") [(.ltE, .name "h")]]
private def secondTest : Expr := .compare (.name "p") [(.ltE, .name "h")]
private def body : List Stmt :=
  [.assign [.tuple [.name "t", .name "p", .name "h"]]
    (.tuple [.call (.name "tri") [.name "i"], .call (.name "pent") [.name "j"], .call (.name "hex") [.name "k"]]),
    .ifThen foundTest [.return (.name "t")] [],
    .ifThen firstTest [.augAssign (.name "i") .add (.constant (.int 1))]
      [.ifThen secondTest [.augAssign (.name "j") .add (.constant (.int 1))]
        [.augAssign (.name "k") .add (.constant (.int 1))]]]
private def searchLoop : Stmt := .whileDo (.constant (.bool true)) body []

private theorem and_evaluate (a b : Prop) [Decidable a] [Decidable b]
    (env : ScalarEnv) (left right : Expr)
    (first : Calls.Evaluates program env left (scalarFlag (decide a)))
    (second : Calls.Evaluates program env right (scalarFlag (decide b))) :
    Calls.Evaluates program env (.boolOp .and [left, right]) (scalarFlag (decide (a ∧ b))) := by
  by_cases accepted : a
  · simp only [accepted, true_and]
    apply Calls.Evaluates.boolean_continue (by simpa only [accepted, decide_true] using first) rfl
    exact Calls.Evaluates.boolean_last second
  · simp only [accepted, false_and, decide_false]
    exact Calls.Evaluates.boolean_stop (by simpa only [accepted, decide_false] using first) rfl

private theorem prepare (i j k : Nat) (env : ScalarEnv) {following : List Stmt} {answerValue : Constant}
    (getI : env "i" = some (scalarNatural i)) (getJ : env "j" = some (scalarNatural j)) (getK : env "k" = some (scalarNatural k))
    (rest : Calls.BlockReturns program (prepared env i j k) following answerValue) :
    Calls.BlockReturns program env (body.take 1 ++ following) answerValue := by
  apply Calls.BlockReturns.unpack (results := values i j k) rfl rfl
  · refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
    · exact Calls.Evaluates.call (.cons (Calls.Evaluates.lookup getI) .nil) (by simpa only [tri_nat] using scalar_tri (i : Int))
    · exact Calls.Evaluates.call (.cons (Calls.Evaluates.lookup getJ) .nil) (by simpa only [pent_nat] using scalar_pent (j : Int))
    · exact Calls.Evaluates.call (.cons (Calls.Evaluates.lookup getK) .nil) (by simpa only [hex_nat] using scalar_hex (k : Int))
  · exact rest

private theorem found_evaluate (after : Int) (t p h : Nat) (env : ScalarEnv)
    (getAfter : env "after" = some (scalarNumber after))
    (getT : env "t" = some (scalarNatural t)) (getP : env "p" = some (scalarNatural p)) (getH : env "h" = some (scalarNatural h)) :
    Calls.Evaluates program env foundTest (scalarFlag (decide (t = p ∧ p = h ∧ after < (t : Int)))) := by
  have equal : Calls.Evaluates program env (.compare (.name "t") [(.eq, .name "p"), (.eq, .name "h")])
      (scalarFlag (decide (t = p ∧ p = h))) := by
    by_cases same : t = p
    · simp only [same, true_and]
      apply Calls.Evaluates.chain (Calls.Evaluates.lookup getT)
      apply Calls.Evaluates.Compares.next (Calls.Evaluates.lookup getP)
        (by simp [scalarCompare, evalCmpOp, same])
      exact Calls.Evaluates.Compares.last (Calls.Evaluates.lookup getH) (by simp [scalarCompare, evalCmpOp])
    · simp only [same, false_and, decide_false]
      apply Calls.Evaluates.chain (Calls.Evaluates.lookup getT)
      exact Calls.Evaluates.Compares.stop (Calls.Evaluates.lookup getP) (by simp [scalarCompare, evalCmpOp, same])
  have later : Calls.Evaluates program env (.compare (.name "t") [(.gt, .name "after")])
      (scalarFlag (decide (after < (t : Int)))) :=
    Calls.Evaluates.compare (Calls.Evaluates.lookup getT) (Calls.Evaluates.lookup getAfter) (by simp [scalarCompare, evalCmpOp])
  simpa only [and_assoc] using and_evaluate _ _ env _ _ equal later

private theorem first_evaluate (t p h : Nat) (env : ScalarEnv)
    (getT : env "t" = some (scalarNatural t)) (getP : env "p" = some (scalarNatural p)) (getH : env "h" = some (scalarNatural h)) :
    Calls.Evaluates program env firstTest (scalarFlag (decide (t ≤ p ∧ t ≤ h))) :=
  and_evaluate _ _ env _ _
    (Calls.Evaluates.compare (Calls.Evaluates.lookup getT) (Calls.Evaluates.lookup getP) (by simp [scalarCompare, evalCmpOp]))
    (Calls.Evaluates.compare (Calls.Evaluates.lookup getT) (Calls.Evaluates.lookup getH) (by simp [scalarCompare, evalCmpOp]))
/-- Cursor bounds prevent skipping the least common value, while their remaining distances decrease. -/
theorem loop (after : Int) (i j k : Nat) (positiveI : 0 < i) (positiveJ : 0 < j) (positiveK : 0 < k)
    (boundI : i ≤ triangleIndex after) (boundJ : j ≤ pentIndex after) (boundK : k ≤ winner after)
    (env : ScalarEnv)
    (getAfter : env "after" = some (scalarNumber after)) (getI : env "i" = some (scalarNatural i))
    (getJ : env "j" = some (scalarNatural j)) (getK : env "k" = some (scalarNatural k)) :
    Calls.BlockReturns program env [searchLoop] (scalarNatural (answer after)) := by
  let ready := prepared env i j k
  have finalAfter : ready "after" = some (scalarNumber after) := by simpa [ready, prepared, Calls.assignNames, values, ScalarEnv.set] using getAfter
  have finalI : ready "i" = some (scalarNatural i) := by simpa [ready, prepared, Calls.assignNames, values, ScalarEnv.set] using getI
  have finalJ : ready "j" = some (scalarNatural j) := by simpa [ready, prepared, Calls.assignNames, values, ScalarEnv.set] using getJ
  have finalK : ready "k" = some (scalarNatural k) := by simpa [ready, prepared, Calls.assignNames, values, ScalarEnv.set] using getK
  have getT : ready "t" = some (scalarNatural (triangular i)) := by simp [ready, prepared, Calls.assignNames, values, ScalarEnv.set]
  have getP : ready "p" = some (scalarNatural (pentagonal j)) := by simp [ready, prepared, Calls.assignNames, values, ScalarEnv.set]
  have getH : ready "h" = some (scalarNatural (hexagonal k)) := by simp [ready, prepared, Calls.assignNames, values, ScalarEnv.set]
  have tested := found_evaluate after (triangular i) (pentagonal j) (hexagonal k) ready finalAfter getT getP getH
  have tBound : triangular i ≤ answer after := by
    simpa only [(triangle_index_spec after).2] using triangular_strictMono.monotone boundI
  have pBound : pentagonal j ≤ answer after := by
    simpa only [(pent_index_spec after).2] using ProjectEulerSolutions.PentagonalDiscriminant.strictMono.monotone boundJ
  have hBound : hexagonal k ≤ answer after := hex_strictMono.monotone boundK
  by_cases found : triangular i = pentagonal j ∧ pentagonal j = hexagonal k ∧ after < (triangular i : Int)
  · rw [decide_eq_true found] at tested
    have later : after < (hexagonal k : Int) := by rw [← found.2.1, ← found.1]; exact found.2.2
    have least := answer_le_common after j k positiveJ positiveK found.2.1 later
    have same : triangular i = answer after := by omega
    apply Calls.BlockReturns.while_loop (value := .bool true) Calls.Evaluates.constant
    apply prepare i j k env getI getJ getK
    apply Calls.BlockReturns.branch tested
    exact Calls.BlockReturns.return_value (Calls.Evaluates.lookup (by simpa only [same] using getT))
  · rw [decide_eq_false found] at tested
    have first := first_evaluate (triangular i) (pentagonal j) (hexagonal k) ready getT getP getH
    have second : Calls.Evaluates program ready secondTest (scalarFlag (decide (pentagonal j ≤ hexagonal k))) :=
      Calls.Evaluates.compare (Calls.Evaluates.lookup getP) (Calls.Evaluates.lookup getH) (by simp [scalarCompare, evalCmpOp])
    by_cases minimumT : triangular i ≤ pentagonal j ∧ triangular i ≤ hexagonal k
    · rw [decide_eq_true minimumT] at first
      have smaller := minimum_before after _ _ _ tBound pBound hBound found minimumT.1 minimumT.2
      have room : i < triangleIndex after := by
        by_contra full
        have same : i = triangleIndex after := by omega
        rw [same, (triangle_index_spec after).2] at smaller
        omega
      let advanced := ready.set "i" (scalarNatural (i + 1))
      have returned := loop after (i + 1) j k (by omega) positiveJ positiveK (by omega) boundJ boundK
        advanced (by simpa [advanced, ScalarEnv.set] using finalAfter) (by simp [advanced, ScalarEnv.set])
        (by simpa [advanced, ScalarEnv.set] using finalJ) (by simpa [advanced, ScalarEnv.set] using finalK)
      apply Calls.BlockReturns.while_loop (value := .bool true) Calls.Evaluates.constant
      apply prepare i j k env getI getJ getK
      apply Calls.BlockReturns.branch tested
      apply Calls.BlockReturns.branch first
      apply Calls.BlockReturns.augAssign (value := scalarNatural (i + 1))
      · exact Calls.Evaluates.binary (Calls.Evaluates.lookup finalI) Calls.Evaluates.constant (by simp [scalarBinary])
      · simpa only [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Bool.false_or, Bool.false_eq_true, if_false, List.nil_append] using returned
    · rw [decide_eq_false minimumT] at first
      by_cases minimumP : pentagonal j ≤ hexagonal k
      · rw [decide_eq_true minimumP] at second
        have pFirst : pentagonal j ≤ triangular i := by omega
        have rejected : ¬ (pentagonal j = triangular i ∧ triangular i = hexagonal k ∧ after < (pentagonal j : Int)) := by
          rintro ⟨same, sameH, later⟩
          exact found ⟨same.symm, same.trans sameH, by simpa only [same] using later⟩
        have smaller := minimum_before after _ _ _ pBound tBound hBound rejected pFirst minimumP
        have room : j < pentIndex after := by
          by_contra full
          have same : j = pentIndex after := by omega
          rw [same, (pent_index_spec after).2] at smaller
          omega
        let advanced := ready.set "j" (scalarNatural (j + 1))
        have returned := loop after i (j + 1) k positiveI (by omega) positiveK boundI (by omega) boundK
          advanced (by simpa [advanced, ScalarEnv.set] using finalAfter) (by simpa [advanced, ScalarEnv.set] using finalI)
          (by simp [advanced, ScalarEnv.set]) (by simpa [advanced, ScalarEnv.set] using finalK)
        apply Calls.BlockReturns.while_loop (value := .bool true) Calls.Evaluates.constant
        apply prepare i j k env getI getJ getK
        apply Calls.BlockReturns.branch tested
        apply Calls.BlockReturns.branch first
        apply Calls.BlockReturns.branch second
        apply Calls.BlockReturns.augAssign (value := scalarNatural (j + 1))
        · exact Calls.Evaluates.binary (Calls.Evaluates.lookup finalJ) Calls.Evaluates.constant (by simp [scalarBinary])
        · simpa only [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            Bool.false_or, Bool.false_eq_true, if_false, List.nil_append] using returned
      · rw [decide_eq_false minimumP] at second
        have hFirst : hexagonal k ≤ triangular i := by omega
        have hSecond : hexagonal k ≤ pentagonal j := by omega
        have rejected : ¬ (hexagonal k = triangular i ∧ triangular i = pentagonal j ∧ after < (hexagonal k : Int)) := by
          rintro ⟨same, sameP, later⟩
          exact found ⟨sameP, (same.trans sameP).symm, by simpa only [same] using later⟩
        have smaller := minimum_before after _ _ _ hBound tBound pBound rejected hFirst hSecond
        have room : k < winner after := by
          by_contra full
          have same : k = winner after := by omega
          rw [same] at smaller
          exact Nat.lt_irrefl _ smaller
        let advanced := ready.set "k" (scalarNatural (k + 1))
        have returned := loop after i j (k + 1) positiveI positiveJ (by omega) boundI boundJ (by omega)
          advanced (by simpa [advanced, ScalarEnv.set] using finalAfter) (by simpa [advanced, ScalarEnv.set] using finalI)
          (by simpa [advanced, ScalarEnv.set] using finalJ) (by simp [advanced, ScalarEnv.set])
        apply Calls.BlockReturns.while_loop (value := .bool true) Calls.Evaluates.constant
        apply prepare i j k env getI getJ getK
        apply Calls.BlockReturns.branch tested
        apply Calls.BlockReturns.branch first
        apply Calls.BlockReturns.branch second
        apply Calls.BlockReturns.augAssign (value := scalarNatural (k + 1))
        · exact Calls.Evaluates.binary (Calls.Evaluates.lookup finalK) Calls.Evaluates.constant (by simp [scalarBinary])
        · simpa only [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            Bool.false_or, Bool.false_eq_true, if_false, List.nil_append] using returned
termination_by triangleIndex after - i + (pentIndex after - j) + (winner after - k)
decreasing_by all_goals omega

/-- The actual three-way merge returns the least common value above every signed threshold. -/
theorem result (after : Int) : Calls.ReturnsValue program "naive" [scalarNumber after] (scalarNatural (answer after)) := by
  apply Calls.BlockReturns.function rfl rfl
  apply Calls.BlockReturns.assign Calls.Evaluates.constant
  apply Calls.BlockReturns.assign Calls.Evaluates.constant
  apply Calls.BlockReturns.assign Calls.Evaluates.constant
  exact loop after 1 1 1 (by decide) (by decide) (by decide)
    (triangle_index_spec after).1 (pent_index_spec after).1 (winner_spec after).1 _ rfl rfl rfl rfl

theorem «Returns» (after : Int) : (Calls.function program "naive" [.int after]).Returns := (result after).returns

theorem «Supported» (after : Int) : (Calls.function program "naive" [.int after]).Supported := («Returns» after).supported

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p45
