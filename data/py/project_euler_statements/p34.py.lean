import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p34.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.SumCalls
import ProjectEulerSolutions.Lib.DigitFactorialBoundCalls
import Mathlib.Data.List.Range

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p34
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.DigitFactorialBase
private abbrev program := P34Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev digits (base n : Nat) : List Mutable.Value := (Nat.digits base n).map number

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 4 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["digit_fact_sum", "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem factorial_eq (n : Nat) : Math.factorial n = Nat.factorial n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Math.factorial, Nat.factorial_succ, ih]

private abbrev factorialExpr : Expr := .call (.name "factorial") [.name "d"]

/-- Every digit is consumed once; the accumulator uses the library factorial recurrence. -/
private theorem digit_loop (values remaining : List Nat) (position total : Nat)
    (heap : Mutable.Heap) (source : SequenceSource) (env : HeapCalls.Env)
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok (values.map number), heap))
    (suffix : values.drop position = remaining)
    (getTotal : env sumAccumulator = some (number total)) :
    BlockReturns program env
      [.sequenceStepLoop "d" source position (sumBody factorialExpr []) [], .return (.name sumAccumulator)]
      heap (number (remaining.foldl (fun acc d => acc + Nat.factorial d) total)) heap := by
  induction remaining generalizing position total env with
  | nil =>
      apply BlockReturns.sequence_done sequence
      · have missing : values[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
        simp [missing]
      · exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | cons head tail ih =>
      have item : values[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      apply BlockReturns.sequence_step (value := number head) sequence (by simp [item])
      apply BlockReturns.assign (value := number (total + Nat.factorial head)) (middle := heap)
      · apply Evaluates.binary (av := number total) (bv := number (Nat.factorial head)) (middle := heap) (afterRight := heap)
          (Evaluates.lookup (by simpa [setLocal, sumAccumulator] using getTotal))
        · apply Evaluates.library_call (values := [number head])
            (.cons (Evaluates.lookup (by simp [setLocal])) .nil) rfl
          change some (Except.map Mutable.Value.scalar (Math.factorialCall [.int head]), heap) = _
          rw [Math.factorialCall_natural, factorial_eq]
          rfl
        · simp [Mutable.binary, scalarBinary, number]
      · change BlockReturns program _
          [.sequenceStepLoop "d" source (position + 1) (sumBody factorialExpr []) [],
            .return (.name sumAccumulator)] heap _ heap
        apply ih
        · simp [List.drop_add_one_eq_tail_drop, suffix]
        · simp [setLocal]

/-- The independent reference consumes the actual digit list in any supported numeral base. -/
theorem digit_fact_sum.result (n base : Nat) (valid : 2 ≤ base) (heap : Mutable.Heap) :
    ReturnsValue program "digit_fact_sum" [number n, number base] heap
      (number (digitSum base n)) (heap ++ [.list (digits base n)]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_sequence (items := digits base n)
    (by intro expressions; simp)
    (Evaluates.call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil))
      ((common.digits_le.result n base (by omega) heap).extend common_extension))
  · simp [Mutable.sequence, digits]
  · exact Evaluates.constant
  · rfl
  · have scanned := digit_loop (Nat.digits base n) (Nat.digits base n) 0 0
      (heap ++ [.list (digits base n)]) (sequenceSource (.ref heap.length))
      (setLocal (comprehensionEnv
        (functionEnv ((findFunctionIn program.body "digit_fact_sum").getD ([], [])).1
          ((findFunctionIn program.body "digit_fact_sum").getD ([], [])).2 [number n, number base] [])
        [("d", .call (.name "digits_le") [.name "n", .name "base"], [])]) sumAccumulator (number 0))
      (by simp [Mutable.sequence, sequenceValue, sequenceSource, digits]) rfl rfl
    simpa only [fold_factorials, Nat.zero_add, digitSum] using scanned

namespace naive
private def boundCondition : Expr := .compare
  (.binOp (.name "base") .pow (.binOp (.name "digits") .sub (.constant (.int 1))))
  [(.ltE, .binOp (.name "digits") .mult (.call (.name "factorial") [.binOp (.name "base") .sub (.constant (.int 1))]))]
private def boundWhile : Stmt := .whileDo boundCondition ProjectEulerSolutions.DigitFactorialBoundCalls.increment []
private def test : Expr := .compare (.call (.name "digit_fact_sum") [.name "n", .name "base"]) [(.eq, .name "n")]
private def body : List Stmt := comprehensionFilters [test] (sumBody (.name "n") [])

private theorem max_factorial (base : Nat) (valid : 2 ≤ base) (env : HeapCalls.Env) (heap : Mutable.Heap)
    (getBase : env "base" = some (number base)) :
    Evaluates program env (.call (.name "factorial") [.binOp (.name "base") .sub (.constant (.int 1))])
      heap (number (maxFact base)) heap := by
  apply Evaluates.library_call (middle := heap) (values := [number (base - 1)])
  · refine .cons ?_ .nil
    apply Evaluates.binary (Evaluates.lookup getBase) Evaluates.constant
    have cast : ((base - 1 : Nat) : Int) = (base : Int) - 1 := by omega
    simp [Mutable.binary, scalarBinary, number, cast]
  · rfl
  · change some (Except.map Mutable.Value.scalar (Math.factorialCall [.int ((base - 1 : Nat) : Int)]), heap) = _
    rw [Math.factorialCall_natural, factorial_eq]
    rfl

private theorem bound_guard (base digits : Nat) (valid : 2 ≤ base) (positive : 1 ≤ digits)
    (env : HeapCalls.Env) (heap : Mutable.Heap)
    (getBase : env "base" = some (number base)) (getDigits : env "digits" = some (number digits)) :
    Evaluates program env boundCondition heap
      (.scalar (.bool (decide (base ^ (digits - 1) ≤ digits * maxFact base)))) heap := by
  apply Evaluates.compare (av := number (base ^ (digits - 1))) (bv := number (digits * maxFact base))
    (middle := heap) (afterRight := heap)
  · apply Evaluates.binary (av := number base) (bv := number (digits - 1))
      (middle := heap) (afterRight := heap) (Evaluates.lookup getBase)
    · apply Evaluates.binary (Evaluates.lookup getDigits) Evaluates.constant
      have cast : ((digits - 1 : Nat) : Int) = (digits : Int) - 1 := by omega
      simp [Mutable.binary, scalarBinary, number, cast]
    · simp [Mutable.binary, scalarBinary, number, show ¬ ((digits - 1 : Nat) : Int) < 0 by omega]
  · exact Evaluates.binary (Evaluates.lookup getDigits) (max_factorial base valid env heap getBase)
      (by simp [Mutable.binary, scalarBinary, number])
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    exact Int.ofNat_le

private theorem tested (base n : Nat) (valid : 2 ≤ base) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getBase : env "base" = some (number base)) (getN : env "n" = some (number n)) :
    Evaluates program env test heap (.scalar (.bool (decide (digitSum base n = n)))) (heap ++ [.list (digits base n)]) := by
  apply Evaluates.compare (av := number (digitSum base n)) (bv := number n)
    (middle := heap ++ [.list (digits base n)]) (afterRight := heap ++ [.list (digits base n)])
  · exact Evaluates.call (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getBase) .nil))
      (digit_fact_sum.result n base valid heap)
  · exact Evaluates.lookup getN
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp]

private theorem scan (base : Nat) (valid : 2 ≤ base) (count first total : Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (getBase : env "base" = some (number base))
    (getTotal : env sumAccumulator = some (number total)) :
    ∃ extra, BlockReturns program env
      [.rangeStepLoop "n" first (first + count) 1 body [], .return (.name sumAccumulator)] heap
      (number (foldValues base (List.range' first count) total)) (heap ++ extra) := by
  induction count generalizing first total heap env with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [foldValues, List.range'_zero, List.foldl_nil, List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues])
      exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let bound := setLocal env "n" (number first)
      let middle := heap ++ [.list (digits base first)]
      have boundBase : bound "base" = some (number base) := by simpa [bound, setLocal] using getBase
      have boundTotal : bound sumAccumulator = some (number total) := by simpa [bound, setLocal, sumAccumulator] using getTotal
      have evaluated := tested base first valid heap bound boundBase (by simp [bound, setLocal])
      by_cases fixed : digitSum base first = first
      · let updated := setLocal bound sumAccumulator (number (total + first))
        obtain ⟨extra, rest⟩ := ih (first + 1) (total + first) middle updated
          (by simpa [updated, setLocal, sumAccumulator] using boundBase) (by simp [updated, setLocal])
        refine ⟨[.list (digits base first)] ++ extra, ?_⟩
        apply BlockReturns.range_step (by simp [Calls.rangeContinues])
        apply BlockReturns.branch (flag := true) (value := .scalar (.bool true)) (by simpa only [fixed, decide_true] using evaluated) rfl
        apply BlockReturns.assign (value := number (total + first)) (middle := middle)
        · exact Evaluates.binary (av := number total) (bv := number first) (middle := middle) (afterRight := middle)
            (Evaluates.lookup boundTotal) (Evaluates.lookup (by simp [setLocal]))
            (by simp [Mutable.binary, scalarBinary, number])
        · simpa [foldValues, List.range'_succ, fixed, body, comprehensionFilters, sumBody, Calls.loopContinuation,
            Calls.loopControl, Calls.loopControlStmt, middle, updated, bound, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm] using rest
      · obtain ⟨extra, rest⟩ := ih (first + 1) total middle bound boundBase boundTotal
        refine ⟨[.list (digits base first)] ++ extra, ?_⟩
        apply BlockReturns.range_step (by simp [Calls.rangeContinues])
        apply BlockReturns.branch (flag := false) (value := .scalar (.bool false)) (by simpa only [fixed, decide_false] using evaluated) rfl
        simpa [foldValues, List.range'_succ, fixed, body, comprehensionFilters, sumBody, Calls.loopContinuation,
          Calls.loopControl, Calls.loopControlStmt, middle, bound, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm] using rest

/-- Both the derived-width loop and every finite counting iteration execute symbolically. -/
theorem result (base : Nat) (valid : 2 ≤ base) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive" [number base] heap (number (answer base valid)) (heap ++ extra) := by
  let initial := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number base] []
  let start := setLocal initial "digits" (number 1)
  obtain ⟨boundedEnv, bounded, width, baseFound⟩ := ProjectEulerSolutions.DigitFactorialBoundCalls.loop program base valid
    boundCondition (fun env => env "base" = some (number base))
    (by intro env heap digits positive current getDigits; exact bound_guard base digits valid positive env heap current getDigits)
    (by intro env digits current; simpa [setLocal] using current)
    1 (by decide) (stopping_spec base valid).1 start heap (by simp [start, setLocal, initial]; rfl) (by simp [start, setLocal])
  let ready := setLocal boundedEnv "upper" (number (upper base valid))
  let generators : List (String × Expr × List Expr) :=
    [("n", .call (.name "range") [.name "base", .binOp (.name "upper") .add (.constant (.int 1))], [test])]
  let summed := setLocal (comprehensionEnv ready generators) sumAccumulator (number 0)
  have upperLarge := upper_ge_base base valid
  obtain ⟨extra, scanned⟩ := scan base valid (upper base valid + 1 - base) base 0 heap summed
    (by simpa [summed, ready, comprehensionEnv, generators, setLocal, sumAccumulator] using baseFound) rfl
  have endPoint : base + (upper base valid + 1 - base) = upper base valid + 1 := by omega
  have endCast : (base : Int) + ((upper base valid + 1 - base : Nat) : Int) = ((upper base valid + 1 : Nat) : Int) := by
    exact_mod_cast endPoint
  rw [endCast, range_answer] at scanned
  have summedResult : Evaluates program ready
      (.sumRange "n" (.name "n") [.name "base", .binOp (.name "upper") .add (.constant (.int 1))] [test])
      heap (number (answer base valid)) (heap ++ extra) := by
    apply Evaluates.sum_range
    apply Evaluates.sum_generator_range (middle := heap) (afterStart := heap) (values := [number base, number (upper base valid + 1)])
    · refine .cons (Evaluates.lookup (by simpa [ready, setLocal] using baseFound)) (.cons ?_ .nil)
      exact Evaluates.binary (av := number (upper base valid)) (bv := number 1) (middle := heap) (afterRight := heap)
        (Evaluates.lookup (by simp [ready, setLocal])) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])
    · rfl
    · exact Evaluates.constant
    · rfl
    · simpa only [summed, generators, body] using scanned
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply bounded.returns
  apply BlockReturns.assign (value := number (upper base valid)) (middle := heap)
  · apply Evaluates.binary (av := number (stoppingWidth base valid - 1)) (bv := number (maxFact base)) (middle := heap) (afterRight := heap)
    · apply Evaluates.binary (Evaluates.lookup width) Evaluates.constant
      have cast : ((stoppingWidth base valid - 1 : Nat) : Int) = (stoppingWidth base valid : Int) - 1 := by
        have positive := (stopping_spec base valid).1; omega
      simp [Mutable.binary, scalarBinary, number, cast]
    · exact max_factorial base valid boundedEnv heap baseFound
    · simp [Mutable.binary, scalarBinary, number, upper]
  · exact BlockReturns.return_value summedResult

private abbrev inputEnv (base : Int) : ScalarEnv := fun name => if name = "base" then some (.int base) else none

theorem «Returns» (base : Int) (condition : Calls.Condition program (inputEnv base) P34Ast.requires_naive_0) :
    (HeapCalls.scalarFunction program "naive" [.int base]).Returns := by
  have valid : 2 ≤ base := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift base to Nat using (by omega : 0 ≤ base)
  obtain ⟨_, returned⟩ := result base (by omega) []
  exact returned.scalar_returns

theorem «Supported» (base : Int) (condition : Calls.Condition program (inputEnv base) P34Ast.requires_naive_0) :
    (HeapCalls.scalarFunction program "naive" [.int base]).Supported := («Returns» base condition).supported

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p34
