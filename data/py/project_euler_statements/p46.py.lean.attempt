import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p46.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.TruthCalls
import ProjectEulerSolutions.Lib.PrimeTwiceSquareSearch

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

namespace can_be_written
private def equation : Expr := .compare
  (.binOp (.name "p") .add (.binOp (.constant (.int 2)) .mult
    (.binOp (.name "k") .pow (.constant (.int 2))))) [(.eq, .name "n")]
private def inner : Expr := .consumeGenerator (.builtinCall .any []) equation
  [(.name "k", .call (.name "range") [.name "n"], [])]
private def outer : Expr := .boolOp .and [.call (.name "is_prime") [.name "p"], inner]

private theorem equation_result (n p k : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n"=some (natural n)) (getP : env "p"=some (natural p))
    (getK : env "k"=some (natural k)) :
    Evaluates program env equation heap (flag (decide (p+2*k^2=n))) heap := by
  apply Evaluates.compare (av := natural (p+2*k^2)) (bv := natural n) (middle := heap) (afterRight := heap)
  · apply Evaluates.binary (av := natural p) (bv := natural (2*k^2)) (middle := heap) (afterRight := heap)
      (Evaluates.lookup getP)
    · exact Evaluates.binary (av := natural 2) (bv := natural (k^2)) (middle := heap) (afterRight := heap)
        Evaluates.constant
        (Evaluates.binary (av := natural k) (bv := natural 2) (middle := heap) (afterRight := heap)
          (Evaluates.lookup getK) Evaluates.constant (by simp [Mutable.binary, scalarBinary]))
        (by simp [Mutable.binary, scalarBinary])
    · simp [Mutable.binary, scalarBinary]
  · exact Evaluates.lookup getN
  · change some (Except.ok (ε := ExceptionObject) (flag (decide (((p+2*k^2 : Nat) : Int)=(n : Int)))), heap)=_
    simp only [Int.natCast_inj]

private theorem inner_result (n p : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n"=some (natural n)) (getP : env "p"=some (natural p)) :
    Evaluates program env inner heap (flag ((List.range n).any (fun k => decide (p+2*k^2=n)))) heap := by
  apply Evaluates.truth_generator_range (universal := false) (values := [natural n])
    (.cons (Evaluates.lookup getN) .nil) rfl
  rw [List.range_eq_range']
  apply any_range_loop (first := 0) (count := n) (stop := n) (invariant := fun inner => inner "n"=some (natural n) ∧ inner "p"=some (natural p))
    (predicate := fun k => decide (p+2*k^2=n))
  · intro inner k valid
    simpa only [setLocal, show ("n"=="k")=false by decide, show ("p"=="k")=false by decide] using valid
  · intro inner k valid getK
    exact equation_result n p k heap inner valid.1 valid.2 getK
  · omega
  · constructor
    · simpa [comprehensionTargetsEnv, targetLocals] using getN
    · simpa [comprehensionTargetsEnv, targetLocals] using getP

private theorem outer_result (n p : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n"=some (natural n)) (getP : env "p"=some (natural p)) :
    Evaluates program env outer heap
      (flag (decide (Nat.Prime p) && (List.range n).any (fun k => decide (p+2*k^2=n)))) heap := by
  have prime : Evaluates program env (.call (.name "is_prime") [.name "p"])
      heap (flag (decide (Nat.Prime p))) heap :=
    Evaluates.call (.cons (Evaluates.lookup getP) .nil) (prime_result p heap)
  by_cases yes : Nat.Prime p
  · simp only [yes, decide_true, Bool.true_and]
    exact Evaluates.boolean_next (flag := true) (by simpa only [yes, decide_true] using prime) rfl rfl
      (Evaluates.boolean_last (inner_result n p heap env getN getP) rfl)
  · simp only [yes, decide_false, Bool.false_and]
    exact Evaluates.boolean_stop (flag := false) (by simpa only [yes, decide_false] using prime) rfl rfl

def written (n : Int) : Bool := if n<0 then false else exhaustive n.toNat

/-- Both nested generators are lazy, allocate no collectors, and terminate for every integer. -/
theorem result (n : Int) (heap : Mutable.Heap) :
    ReturnsValue program "can_be_written" [number n] heap (flag (written n)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.truth_generator_range (universal := false) (values := [number n])
    (.cons (Evaluates.lookup rfl) .nil) rfl
  by_cases negative : n<0
  · apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    simpa only [written, if_pos negative] using
      (BlockReturns.return_value (module := program) (heap := heap) (env := _)
        (Evaluates.constant (value := .bool false)))
  · lift n to Nat using (by omega : 0≤n)
    simp only [written, if_neg (by omega : ¬ (n : Int)<0), Int.toNat_natCast, exhaustive]
    rw [List.range_eq_range']
    apply any_range_loop (first := 0) (count := n) (stop := n) (invariant := fun inner => inner "n"=some (natural n))
      (predicate := fun p => decide (Nat.Prime p) && (List.range' 0 n).any (fun k => decide (p+2*k^2=n)))
    · intro inner p valid
      simpa [setLocal] using valid
    · intro inner p valid getP
      simpa only [List.range_eq_range'] using outer_result n p heap inner valid getP
    · omega
    · simp [comprehensionTargetsEnv, targetLocals, functionEnv]
      rfl

theorem «Returns» (n : Int) : (HeapCalls.scalarFunction program "can_be_written" [.int n]).Returns :=
  (result n []).scalar_returns

theorem «Supported» (n : Int) : (HeapCalls.scalarFunction program "can_be_written" [.int n]).Supported :=
  («Returns» n).supported
end can_be_written

namespace naive
private def predicate : Expr := .boolOp .and
  [.call (.name "is_odd_composite") [.name "n"],
    .unaryOp .not (.call (.name "can_be_written") [.name "n"])]
private def body : List Stmt := [.ifThen predicate [.return (.name "n")] []]

def answer (limit : Int) : Nat := ((List.range limit.toNat).find? counterexample).getD 0

private theorem tested (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n"=some (natural n)) :
    Evaluates program env predicate heap (flag (counterexample n)) heap := by
  have odd : Evaluates program env (.call (.name "is_odd_composite") [.name "n"])
      heap (flag (oddComposite n)) heap :=
    Evaluates.call (.cons (Evaluates.lookup getN) .nil) (is_odd_composite.result n heap)
  have written : Evaluates program env (.unaryOp .not (.call (.name "can_be_written") [.name "n"]))
      heap (flag (!fast n)) heap := by
    apply Evaluates.unary
    · apply Evaluates.call (.cons (Evaluates.lookup getN) .nil)
      simpa only [can_be_written.written, if_neg (Int.not_lt.mpr (Int.natCast_nonneg n)),
        Int.toNat_natCast, ← fast_correct] using can_be_written.result (n : Int) heap
    · rfl
  cases keep : oddComposite n with
  | false =>
      simp only [counterexample, keep, Bool.false_and]
      exact Evaluates.boolean_stop (flag := false) (by simpa only [keep] using odd) rfl rfl
  | true =>
      simp only [counterexample, keep, Bool.true_and]
      exact Evaluates.boolean_next (flag := true) (by simpa only [keep] using odd) rfl rfl
        (Evaluates.boolean_last written rfl)

private theorem loop (first count stop : Nat) (length : first+count=stop)
    (heap : Mutable.Heap) (env : HeapCalls.Env) :
    BlockReturns program env
      [.rangeStepLoop "n" first stop 1 body [], .return (.constant (.int 0))]
      heap (natural (((List.range' first count).find? counterexample).getD 0)) heap := by
  induction count generalizing first env with
  | zero =>
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value Evaluates.constant
  | succ count ih =>
      let bound := setLocal env "n" (natural first)
      have compared := tested first heap bound rfl
      rw [List.range'_succ, List.find?_cons]
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      cases accepted : counterexample first with
      | true =>
          simp only [Option.getD_some]
          apply BlockReturns.branch (flag := true) (by simpa only [accepted] using compared) rfl
          exact BlockReturns.return_value (Evaluates.lookup rfl)
      | false =>
          apply BlockReturns.branch (flag := false) (by simpa only [accepted] using compared) rfl
          have rest := ih (first+1) (by omega) bound
          simpa only [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            Bool.false_or, Bool.false_eq_true, if_false, List.nil_append,
            Int.natCast_add, Int.natCast_one] using rest

/-- The exhaustive reference returns its first counterexample, or zero for an empty search. -/
theorem result (limit : Int) (heap : Mutable.Heap) :
    ReturnsValue program "naive" [number limit] heap (natural (answer limit)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.for_range (.cons (Evaluates.lookup rfl) .nil) rfl
  by_cases negative : limit<0
  · apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    have empty : limit.toNat=0 := Int.toNat_eq_zero.mpr (by omega)
    simpa only [answer, empty, List.range_zero, List.find?_nil, Option.getD_none] using
      (BlockReturns.return_value (module := program) (heap := heap) (env := _)
        (Evaluates.constant (value := .int 0)))
  · lift limit to Nat using (by omega : 0≤limit)
    simpa only [answer, Int.toNat_natCast, List.range_eq_range'] using loop 0 limit limit (by omega) heap _

theorem «Returns» (limit : Int) : (HeapCalls.scalarFunction program "naive" [.int limit]).Returns :=
  (result limit []).scalar_returns

theorem «Supported» (limit : Int) : (HeapCalls.scalarFunction program "naive" [.int limit]).Supported :=
  («Returns» limit).supported
end naive

namespace naive_default
/-- The finite certificate proves that the reference window contains the global first counterexample. -/
theorem result (heap : Mutable.Heap) :
    ReturnsValue program "naive_default" [] heap
      (natural ProjectEulerSolutions.PrimeTwiceSquareSearch.winner) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.call (.cons Evaluates.constant .nil)
  have reference := naive.result 10000 heap
  simpa only [naive.answer, show (10000 : Int).toNat=10000 by rfl,
    ProjectEulerSolutions.PrimeTwiceSquareSearch.reference_find, Option.getD_some] using reference

theorem «Returns» : (HeapCalls.scalarFunction program "naive_default" []).Returns :=
  (result []).scalar_returns

theorem «Supported» : (HeapCalls.scalarFunction program "naive_default" []).Supported :=
  «Returns».supported
end naive_default

end data.«project-euler-statements».data.py.project_euler_statements.p46
