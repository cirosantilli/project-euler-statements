import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p47.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.SumCalls
import lang.py.FormalSW.TruthCalls
import ProjectEulerSolutions.Lib.ConsecutiveFactors

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p47
open FormalSW.PyAst
open ProjectEulerStatements.P47
private abbrev program := P47Ast.module

private theorem common_scalar_extension : Calls.Extends program CommonAst.module := by
  change Calls.Extends { body := program.body.take 4++CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["num_distinct_prime_factors", "naive", "naive_solver"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem common_extension : HeapCalls.Extends program CommonAst.module :=
  HeapCalls.Extends.of_classless (classless := rfl) common_scalar_extension

private def factor (n p : Nat) : Bool := decide (2≤p ∧ n%p=0 ∧ Nat.Prime p)
private def selected (n first count : Nat) : Nat := ((List.range' first count).filter (factor n)).length
private def filterExpression : Expr := .boolOp .and [
  .compare (.name "p") [(.gtE, .constant (.int 2))],
  .compare (.binOp (.name "n") .mod (.name "p")) [(.eq, .constant (.int 0))],
  .call (.name "is_prime") [.name "p"]]

namespace ScalarCount
open Calls

private theorem tested (n p : Nat) (env : ScalarEnv)
    (getN : env "n"=some (.int n)) (getP : env "p"=some (.int p)) :
    Evaluates program env filterExpression (.bool (factor n p)) := by
  have large : Evaluates program env (.compare (.name "p") [(.gtE, .constant (.int 2))])
      (.bool (decide (2≤p))) := by
    apply Evaluates.compare (Evaluates.lookup getP) Evaluates.constant
    change some (decide ((2 : Int)≤(p : Int)))=_
    change some (decide (((2 : Nat) : Int)≤(p : Int)))=_
    simp only [Int.ofNat_le]
  by_cases lower : 2≤p
  · apply Evaluates.boolean_continue (by simpa only [lower, decide_true] using large) rfl
    have divisible : Evaluates program env (.compare (.binOp (.name "n") .mod (.name "p")) [(.eq, .constant (.int 0))])
        (.bool (decide (n%p=0))) := by
      apply Evaluates.compare (av := .int (n%p)) (bv := .int 0)
      · exact Evaluates.binary (Evaluates.lookup getN) (Evaluates.lookup getP)
          (by simp [scalarBinary, show p≠0 by omega, show 0<p by omega])
      · exact Evaluates.constant
      · change some (decide (((n%p : Nat) : Int)=0))=_
        simp only [Int.natCast_eq_zero]
    by_cases divides : n%p=0
    · apply Evaluates.boolean_continue (by simpa only [divides, decide_true] using divisible) rfl
      apply Evaluates.boolean_last
      simpa only [factor, lower, divides, true_and] using
        Evaluates.call (.cons (Evaluates.lookup getP) .nil) ((common.is_prime.result p).extend common_scalar_extension)
    · simp only [factor, lower, divides, false_and, and_false, decide_false]
      exact Evaluates.boolean_stop (by simpa only [divides, decide_false] using divisible) rfl
  · simp only [factor, lower, false_and, decide_false]
    exact Evaluates.boolean_stop (by simpa only [lower, decide_false] using large) rfl

private theorem sum_loop (n first count total : Nat) (env : ScalarEnv) (getN : env "n"=some (.int n)) :
    SumReturns program ⟨"p", .constant (.int 1), [filterExpression], first+count, 1, env⟩ first total
      (total+selected n first count) := by
  induction count generalizing first total with
  | zero =>
      simpa [selected] using SumReturns.done (module := program)
        (sum := ⟨"p", .constant (.int 1), [filterExpression], first, 1, env⟩)
        (next := first) (total := total) (by simp [rangeContinues])
  | succ count ih =>
      have compared := Evaluates.boolean_last (op := .and)
        (tested n first (env.set "p" (.int first)) (by simpa [ScalarEnv.set] using getN) (by simp [ScalarEnv.set]))
      cases yes : factor n first with
      | false =>
          apply SumReturns.skip (by simp [rangeContinues]) (by simpa only [yes] using compared) rfl
          simpa [selected, List.range'_succ, yes, Nat.add_assoc, Int.add_assoc, Int.add_comm, Int.add_left_comm] using ih (first+1) total
      | true =>
          apply SumReturns.keep (by simp [rangeContinues]) (by simpa only [yes] using compared) rfl
            (item := .int 1) (updated := total+1) Evaluates.constant rfl
          simpa [selected, List.range'_succ, yes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm] using ih (first+1) (total+1)

/-- Scalar calls execute the guarded filtered sum, including its primality calls. -/
theorem result (n : Nat) :
    ReturnsValue program "num_distinct_prime_factors" [.int n] (.int (numDistinctPrimeFactors n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range (values := [.int (n+1)])
    (.cons (Evaluates.binary (av := .int n) (bv := .int 1) (Evaluates.lookup rfl) Evaluates.constant
      (by simp [scalarBinary])) .nil) rfl
  have counted := sum_loop n 0 (n+1) 0
    (argumentEnv ((findFunctionIn program.body "num_distinct_prime_factors").getD ([], [])).1 [.int n]) rfl
  simpa only [selected, numDistinctPrimeFactors, factor, ← List.range_eq_range', Nat.zero_add,
    Int.natCast_add, Int.natCast_one, Int.natCast_zero, Int.zero_add] using counted

private theorem negative (n : Int) (below : n<0) :
    ReturnsValue program "num_distinct_prime_factors" [.int n] (.int 0) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range (values := [.int (n+1)])
    (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil) rfl
  exact SumReturns.done (by simp [rangeContinues]; omega)
end ScalarCount

theorem num_distinct_prime_factors.«Returns» (n : Int) :
    (Calls.function program "num_distinct_prime_factors" [.int n]).Returns := by
  by_cases below : n<0
  · exact (ScalarCount.negative n below).returns
  · lift n to Nat using (by omega : 0≤n)
    exact (ScalarCount.result n).returns

namespace HeapCount
open HeapCalls
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)

private theorem tested (n p : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n"=some (number n)) (getP : env "p"=some (number p)) :
    Evaluates program env filterExpression heap (flag (factor n p)) heap := by
  have large : Evaluates program env (.compare (.name "p") [(.gtE, .constant (.int 2))])
      heap (flag (decide (2≤p))) heap := by
    apply Evaluates.compare (av := number p) (bv := number 2) (middle := heap) (afterRight := heap)
      (Evaluates.lookup getP) Evaluates.constant
    change some (Except.ok (ε := ExceptionObject) (flag (decide (((2 : Nat) : Int)≤(p : Int)))), heap)=_
    simp only [Int.ofNat_le]
  by_cases lower : 2≤p
  · apply Evaluates.boolean_next (by simpa only [lower, decide_true] using large) rfl rfl
    have divisible : Evaluates program env (.compare (.binOp (.name "n") .mod (.name "p")) [(.eq, .constant (.int 0))])
        heap (flag (decide (n%p=0))) heap := by
      apply Evaluates.compare (av := number (n%p)) (bv := number 0) (middle := heap) (afterRight := heap)
      · exact Evaluates.binary (Evaluates.lookup getN) (Evaluates.lookup getP)
          (by simp [Mutable.binary, scalarBinary, number, show p≠0 by omega, show 0<p by omega])
      · exact Evaluates.constant
      · change some (Except.ok (ε := ExceptionObject) (flag (decide (((n%p : Nat) : Int)=0))), heap)=_
        simp only [Int.natCast_eq_zero]
    by_cases divides : n%p=0
    · apply Evaluates.boolean_next (by simpa only [divides, decide_true] using divisible) rfl rfl
      apply Evaluates.boolean_last (truth := rfl)
      simpa only [factor, lower, divides, true_and] using
        Evaluates.call (.cons (Evaluates.lookup getP) .nil) ((common.is_prime.heap_result p heap).extend common_extension)
    · simp only [factor, lower, divides, false_and, and_false, decide_false]
      exact Evaluates.boolean_stop (by simpa only [divides, decide_false] using divisible) rfl rfl
  · simp only [factor, lower, false_and, decide_false]
    exact Evaluates.boolean_stop (by simpa only [lower, decide_false] using large) rfl rfl

private theorem sum_loop (n first count total stop : Nat) (length : first+count=stop)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (getN : env "n"=some (number n))
    (accumulator : env sumAccumulator=some (number total)) :
    BlockReturns program env
      [.rangeStepLoop "p" first stop 1 (comprehensionFilters [filterExpression] (sumBody (.constant (.int 1)) [])) [],
        .return (.name sumAccumulator)] heap (number (total+selected n first count)) heap := by
  induction count generalizing first total env with
  | zero =>
      simp only [selected, List.range'_zero, List.filter_nil, List.length_nil, Nat.add_zero]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup accumulator)
  | succ count ih =>
      let bound := setLocal env "p" (number first)
      have boundN : bound "n"=some (number n) := by simpa [bound, setLocal] using getN
      have saved : bound sumAccumulator=some (number total) := by simpa [bound, setLocal] using accumulator
      have compared := tested n first heap bound boundN rfl
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      cases yes : factor n first with
      | false =>
          apply BlockReturns.branch (flag := false) (by simpa only [yes] using compared) rfl
          have rest := ih (first+1) total (by omega) bound boundN saved
          simpa [selected, List.range'_succ, yes, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt, comprehensionFilters, sumBody] using rest
      | true =>
          apply BlockReturns.branch (flag := true) (by simpa only [yes] using compared) rfl
          apply BlockReturns.assign (value := number (total+1)) (middle := heap)
          · exact Evaluates.binary (av := number total) (bv := number 1)
              (Evaluates.lookup saved) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])
          · let updated := setLocal bound sumAccumulator (number (total+1))
            have rest := ih (first+1) (total+1) (by omega) updated (by simpa [updated, setLocal] using boundN) rfl
            simpa [selected, List.range'_succ, yes, Calls.loopContinuation, Calls.loopControl,
              Calls.loopControlStmt, comprehensionFilters, sumBody, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest

/-- The same finite count executes in the heap interpreter without allocating a collector. -/
theorem result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "num_distinct_prime_factors" [number n] heap (number (numDistinctPrimeFactors n)) heap := by
  let initial := functionEnv ((findFunctionIn program.body "num_distinct_prime_factors").getD ([], [])).1
    ((findFunctionIn program.body "num_distinct_prime_factors").getD ([], [])).2 [number n] []
  let inner := setLocal (comprehensionEnv initial [("p", .call (.name "range")
    [.binOp (.name "n") .add (.constant (.int 1))], [filterExpression])]) sumAccumulator (number 0)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range (values := [number (n+1)])
    (.cons (Evaluates.binary (av := number n) (bv := number 1) (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup rfl) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])) .nil)
    rfl Evaluates.constant rfl
  have counted := sum_loop n 0 (n+1) 0 (n+1) (by omega) heap inner
    (by simp [inner, comprehensionEnv, setLocal]; rfl) rfl
  simpa only [selected, numDistinctPrimeFactors, factor, ← List.range_eq_range', Nat.zero_add,
    Int.natCast_add, Int.natCast_one] using counted
end HeapCount

namespace naive
open HeapCalls ProjectEulerSolutions.ConsecutiveFactors
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private def element : Expr := .compare
  (.call (.name "num_distinct_prime_factors") [.binOp (.name "i") .add (.name "j")]) [(.eq, .name "n")]
private def condition : Expr := .consumeGenerator (.builtinCall .all []) element
  [(.name "j", .call (.name "range") [.name "n"], [])]
private abbrev body : List Stmt :=
  [.ifThen condition [.return (.name "i")] [], .augAssign (.name "i") .add (.constant (.int 1))]

private theorem tested (k first : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n"=some (number k)) (getI : env "i"=some (number first)) :
    Evaluates program env condition heap (flag (run k first)) heap := by
  rw [run_statement]
  apply Evaluates.truth_generator_range (universal := true) (values := [number k])
    (.cons (Evaluates.lookup getN) .nil) rfl
  rw [List.range_eq_range']
  apply all_range_loop (first := 0) (count := k) (stop := k)
    (invariant := fun inner => inner "n"=some (number k) ∧ inner "i"=some (number first))
    (predicate := fun j => decide (numDistinctPrimeFactors (first+j)=k))
  · intro inner j valid
    simpa [setLocal] using valid
  · intro inner j valid getJ
    apply Evaluates.compare (av := number (numDistinctPrimeFactors (first+j))) (bv := number k)
      (middle := heap) (afterRight := heap)
    · apply Evaluates.call (values := [number (first+j)]) (.cons
        (Evaluates.binary (av := number first) (bv := number j) (middle := heap) (afterRight := heap) (finalHeap := heap)
          (Evaluates.lookup valid.2) (Evaluates.lookup getJ) (by simp [Mutable.binary, scalarBinary, number])) .nil)
      exact HeapCount.result (first+j) heap
    · exact Evaluates.lookup valid.1
    · change some (Except.ok (ε := ExceptionObject)
        (flag (decide (((numDistinctPrimeFactors (first+j) : Nat) : Int)=(k : Int)))), heap)=_
      simp only [Int.natCast_inj]
  · omega
  · constructor
    · simpa [comprehensionTargetsEnv, targetLocals] using getN
    · simpa [comprehensionTargetsEnv, targetLocals] using getI

private theorem loop (k first : Nat) (before : first≤least k) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n"=some (number k)) (getI : env "i"=some (number first)) :
    BlockReturns program env [.whileDo (.constant (.bool true)) body []] heap (number (least k)) heap := by
  have compared := tested k first heap env getN getI
  by_cases accepted : run k first=true
  · have minimal := Nat.find_min' (exists_consecutive_with_n_factors k)
      (by simpa only [run_statement] using accepted)
    have same : first=least k := by dsimp [least, ProjectEulerStatements.P47.naive] at *; omega
    apply BlockReturns.while_loop (flag := true) Evaluates.constant rfl
    apply BlockReturns.branch (flag := true) (by simpa only [accepted] using compared) rfl
    exact BlockReturns.return_value (Evaluates.lookup (by simpa only [same] using getI))
  · have earlier : first<least k := by
      have winner := least_accepted k
      by_contra late
      have same : first=least k := by omega
      exact accepted (same ▸ winner)
    have rejected : run k first=false := by cases value : run k first <;> simp_all
    let next := setLocal env "i" (number (first+1))
    have rest := loop k (first+1) (by omega) heap next (by simpa [next, setLocal] using getN) rfl
    apply BlockReturns.while_loop (flag := true) Evaluates.constant rfl
    apply BlockReturns.branch (flag := false) (by simpa only [rejected] using compared) rfl
    apply BlockReturns.augAssign (value := number (first+1)) (middle := heap) (afterOperation := heap)
      getI Evaluates.constant
    · simp [inplace, Mutable.binary, scalarBinary, number]
    · simpa [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using rest
termination_by least k-first

decreasing_by omega

/-- The original unbounded reference reaches its mathematical least run, conditional on the statement axiom. -/
theorem result (k : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "naive" [number k] heap (number (least k)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  exact loop k 0 (Nat.zero_le _) heap _ (by simp [setLocal]; rfl) rfl

private theorem negative (k : Int) (below : k<0) (heap : Mutable.Heap) :
    ReturnsValue program "naive" [.scalar (.int k)] heap (number 0) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.while_loop (flag := true) Evaluates.constant rfl
  apply BlockReturns.branch (value := flag true) (flag := true)
  · apply Evaluates.truth_generator_range (universal := true) (values := [.scalar (.int k)])
      (.cons (Evaluates.lookup (by simp [setLocal]; rfl)) .nil) rfl
    apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockReturns.return_value Evaluates.constant
  · rfl
  · exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem «Returns» (k : Int) : (HeapCalls.scalarFunction program "naive" [.int k]).Returns := by
  by_cases below : k<0
  · exact (negative k below []).scalar_returns
  · lift k to Nat using (by omega : 0≤k)
    exact (result k []).scalar_returns

theorem «Supported» (k : Int) : (HeapCalls.scalarFunction program "naive" [.int k]).Supported :=
  («Returns» k).supported
end naive

namespace naive_solver
open HeapCalls ProjectEulerSolutions.ConsecutiveFactors
/-- The adapter preserves the original diagonal reference while accepting the solver's tuning parameter. -/
theorem result (k : Nat) (runLength startLimit : Int) (heap : Mutable.Heap) :
    ReturnsValue program "naive_solver" [.scalar (.int k), .scalar (.int runLength), .scalar (.int startLimit)] heap
      (.scalar (.int (least k))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (naive.result k heap)

theorem «Returns» (k runLength startLimit : Int) :
    (HeapCalls.scalarFunction program "naive_solver" [.int k, .int runLength, .int startLimit]).Returns := by
  by_cases below : k<0
  · have returned : ReturnsValue program "naive_solver" [.scalar (.int k), .scalar (.int runLength), .scalar (.int startLimit)]
        [] (.scalar (.int 0)) [] := by
      apply BlockReturns.function rfl rfl
      apply BlockReturns.return_value
      exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (naive.negative k below [])
    exact returned.scalar_returns
  · lift k to Nat using (by omega : 0≤k)
    exact (result k runLength startLimit []).scalar_returns

theorem «Supported» (k runLength startLimit : Int) :
    (HeapCalls.scalarFunction program "naive_solver" [.int k, .int runLength, .int startLimit]).Supported :=
  («Returns» k runLength startLimit).supported
end naive_solver

end data.«project-euler-statements».data.py.project_euler_statements.p47
