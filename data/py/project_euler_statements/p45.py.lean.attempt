import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p45.py.ast»
import lang.py.FormalSW.TruthCalls
import ProjectEulerSolutions.Lib.TriPentHex
import ProjectEulerSolutions.Lib.TriPentHexSearch

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

def valueTest (x : Int) : Bool := pentTest x && hexValueTest x
def indexTest (index : Int) : Bool := valueTest (triPolynomial index)
def firstResult (indices : List Int) : Int := ((indices.find? indexTest).map triPolynomial).getD 0

theorem pentTest_nat (n : Nat) : pentTest n=isPent n := by
  simp [pentTest, membership, isPent, show ¬ (n : Int)<0 by omega]
  rfl

theorem hexValueTest_nat (n : Nat) : hexValueTest n=isHex n := by
  simp [hexValueTest, membership, isHex, show ¬ (n : Int)<0 by omega]
  rfl

theorem indexTest_nat (n : Nat) : indexTest n=common n := by
  simp only [indexTest, valueTest, tri_nat, pentTest_nat, hexValueTest_nat, common]

/-- Mapping integer source indices retains the mathematical first match and exact polynomial value. -/
theorem firstResult_nat (indices : List Nat) :
    firstResult (indices.map fun n : Nat => (n : Int)) =
      ((((indices.find? common).map triangular).getD 0 : Nat) : Int) := by
  cases selected : indices.find? common <;>
    simp [firstResult, List.find?_map, Function.comp_def, indexTest_nat, selected, tri_nat]

namespace naive
private def predicate : Expr := .boolOp .and [.call (.name "is_pent") [.name "t"], .call (.name "is_hex") [.name "t"]]
private def body : List Stmt :=
  [.assign [.name "t"] (.call (.name "tri") [.binOp (.name "start") .add (.name "i")]),
    .ifThen predicate [.return (.name "t")] []]

private theorem predicate_result (x : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getT : env "t" = some (number x)) :
    Evaluates program env predicate heap (flag (valueTest x)) heap := by
  have first := Evaluates.call (.cons (Evaluates.lookup getT) .nil) (is_pent.result x heap)
  have second := Evaluates.call (.cons (Evaluates.lookup getT) .nil) (is_hex.result x heap)
  cases accepted : pentTest x with
  | false =>
      simp only [valueTest, accepted, Bool.false_and]
      exact Evaluates.boolean_stop (flag := false) (by simpa only [accepted] using first) rfl rfl
  | true =>
      simp only [valueTest, accepted, Bool.true_and]
      exact Evaluates.boolean_next (flag := true) (by simpa only [accepted] using first) rfl rfl
        (Evaluates.boolean_last second rfl)

/-- The finite reference scan returns its first accepted triangular value, with the heap unchanged. -/
theorem loop (start : Int) (first count stop : Nat) (equation : first+count=stop)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (getStart : env "start" = some (number start)) :
    BlockReturns program env [.rangeStepLoop "i" first stop 1 body [], .return (.constant (.int 0))] heap
      (number (firstResult ((List.range' first count).map fun i : Nat => start+(i : Int)))) heap := by
  induction count generalizing first env with
  | zero =>
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value Evaluates.constant
  | succ count ih =>
      let bound := setLocal env "i" (natural first)
      let ready := setLocal bound "t" (number (triPolynomial (start+first)))
      have assigned : Evaluates program bound (.call (.name "tri") [.binOp (.name "start") .add (.name "i")])
          heap (number (triPolynomial (start+first))) heap :=
        Evaluates.call (.cons (Evaluates.binary (av := number start) (bv := natural first) (middle := heap) (afterRight := heap)
          (Evaluates.lookup (by simpa [bound, setLocal] using getStart)) (Evaluates.lookup (by simp [bound, setLocal])) rfl) .nil)
          (tri.result (start+first) heap)
      have tested : Evaluates program ready predicate heap (flag (indexTest (start+first))) heap :=
        predicate_result (triPolynomial (start+first)) heap ready (by simp [ready, setLocal])
      rw [List.range'_succ, List.map_cons]
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      apply BlockReturns.assign assigned
      cases accepted : indexTest (start+first) with
      | true =>
          simp only [firstResult, List.find?_cons, accepted, Option.map_some, Option.getD_some]
          apply BlockReturns.branch (flag := true) tested (by simp [Mutable.truth, scalarTruth, accepted])
          exact BlockReturns.return_value (Evaluates.lookup (by simp [ready, setLocal]))
      | false =>
          simp only [firstResult, List.find?_cons, accepted]
          apply BlockReturns.branch (flag := false) tested (by simp [Mutable.truth, scalarTruth, accepted])
          have rest := ih (first+1) (by omega) ready (by simpa [ready, bound, setLocal] using getStart)
          simpa only [Calls.loopContinuation, show Calls.loopControl body = false from rfl, Bool.false_eq_true, if_false,
            List.nil_append, Int.natCast_add, Int.natCast_one] using rest

/-- Every integer start and finite bound is supported, including a negative bound with no iterations. -/
theorem result (start limit : Int) (heap : Mutable.Heap) :
    ReturnsValue program "naive" [number start, number limit] heap
      (number (firstResult ((List.range ((limit+1).toNat)).map fun i : Nat => start+(i : Int)))) heap := by
  let initial := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number start, number limit] []
  apply BlockReturns.function rfl rfl
  apply BlockReturns.for_range (values := [number (limit+1)])
    (.cons (Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup rfl) Evaluates.constant rfl) .nil) rfl
  by_cases negative : limit < 0
  · have empty : (limit+1).toNat=0 := by omega
    simp only [empty, List.range_zero, List.map_nil, firstResult, List.find?_nil, Option.map_none, Option.getD_none]
    exact BlockReturns.range_done (by simp [Calls.rangeContinues]; omega) (BlockReturns.return_value Evaluates.constant)
  · lift limit to Nat using (by omega : 0 ≤ limit)
    have executed := loop start 0 (limit+1) (limit+1) (by omega) heap initial rfl
    simpa only [List.range_eq_range', Int.toNat_natCast, ← Int.natCast_add, Int.natCast_one] using executed

theorem «Returns» (start limit : Int) : (HeapCalls.scalarFunction program "naive" [.int start, .int limit]).Returns :=
  (result start limit []).scalar_returns

theorem «Supported» (start limit : Int) : (HeapCalls.scalarFunction program "naive" [.int start, .int limit]).Supported :=
  («Returns» start limit).supported
end naive

namespace naive_default
/-- The fixed reference window is evaluated by the generic source proof, not by exhaustive execution. -/
theorem result (heap : Mutable.Heap) :
    ReturnsValue program "naive_default" [] heap
      (number (firstResult ((List.range 100001).map fun i : Nat => (286 : Int)+(i : Int)))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call (.cons Evaluates.constant (.cons Evaluates.constant .nil)) (naive.result 286 100000 heap)

/-- The certified first match lies inside the finite reference window. -/
theorem search_result (heap : Mutable.Heap) :
    ReturnsValue program "naive_default" [] heap (natural (hexagonal ProjectEulerSolutions.TriPentHexSearch.winner)) heap := by
  have shifted : (List.range 100001).map (fun i : Nat => (286 : Int)+(i : Int)) =
      (List.range' 286 100001).map (fun i : Nat => (i : Int)) := by
    simp only [List.range'_eq_map_range, List.map_map, Function.comp_def, Int.natCast_add]
    rfl
  have same : firstResult ((List.range 100001).map fun i : Nat => (286 : Int)+(i : Int)) =
      (hexagonal ProjectEulerSolutions.TriPentHexSearch.winner : Int) := by
    rw [shifted, firstResult_nat, ProjectEulerSolutions.TriPentHexSearch.reference_find]
    simp only [Option.map_some, Option.getD_some, ProjectEulerSolutions.TriPentHexSearch.triangleIndex,
      hex_triangular ProjectEulerSolutions.TriPentHexSearch.winner (by decide)]
  simpa only [same] using result heap

theorem «Returns» : (HeapCalls.scalarFunction program "naive_default" []).Returns :=
  (result []).scalar_returns

theorem «Supported» : (HeapCalls.scalarFunction program "naive_default" []).Supported := «Returns».supported
end naive_default

end data.«project-euler-statements».data.py.project_euler_statements.p45
