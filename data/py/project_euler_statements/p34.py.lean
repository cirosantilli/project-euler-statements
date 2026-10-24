import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p34.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.SumCalls
import ProjectEulerStatements.P34
import Mathlib.Data.List.Range

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p34
open FormalSW.PyAst HeapCalls
private abbrev program := P34Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev digits (n : Nat) : List Mutable.Value := (Nat.digits 10 n).map number

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

theorem digit_fact_sum.result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "digit_fact_sum" [number n] heap
      (number (ProjectEulerStatements.P34.digitFactSum n)) (heap ++ [.list (digits n)]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_sequence (items := digits n)
    (by intro expressions; simp)
    (Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
      ((common.digits_le.decimal n heap).extend common_extension))
  · simp [Mutable.sequence, digits]
  · exact Evaluates.constant
  · rfl
  · apply digit_loop (Nat.digits 10 n) (Nat.digits 10 n) 0 0
    · simp [Mutable.sequence, sequenceValue, sequenceSource]
    · rfl
    · rfl

private abbrev accepted (n : Nat) : Prop :=
  n ≠ 1 ∧ n ≠ 2 ∧ ProjectEulerStatements.P34.digitFactSum n = n
private abbrev excluded : Expr :=
  .membership (.name "n") (.tuple [.constant (.int 1), .constant (.int 2)]) true
private abbrev test : Expr := .boolOp .and
  [excluded, .compare (.call (.name "digit_fact_sum") [.name "n"]) [(.eq, .name "n")]]
private abbrev body : List Stmt := comprehensionFilters [test] (sumBody (.name "n") [])

/-- Membership allocates its tuple before short-circuiting the factorial test. -/
private theorem test_result (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) :
    ∃ finalHeap, Evaluates program env test heap (.scalar (.bool (decide (accepted n)))) finalHeap := by
  let middle := heap ++ [.tuple [number 1, number 2]]
  have first : Evaluates program env excluded heap
      (.scalar (.bool (decide (n ≠ 1 ∧ n ≠ 2)))) middle := by
    apply Evaluates.membership (needle := number n) (source := .ref heap.length) (middle := middle)
      (.cons (Evaluates.lookup getN)
        (.cons (Evaluates.tuple (values := [number 1, number 2]) (.cons Evaluates.constant (.cons Evaluates.constant .nil)) (by decide)) .nil))
    by_cases one : n = 1
    · subst n
      simp [HeapCalls.membership, sequenceContains, middle, number, Except.map]
    · by_cases two : n = 2
      · subst n
        simp [HeapCalls.membership, sequenceContains, middle, number,
          HeapCalls.compare, scalarCompare, evalCmpOp, Mutable.truth, Except.map]
      · have castOne : (n : Int) ≠ 1 := by exact_mod_cast one
        have castTwo : (n : Int) ≠ 2 := by exact_mod_cast two
        simp [HeapCalls.membership, sequenceContains, middle, number,
          HeapCalls.compare, scalarCompare, evalCmpOp, Mutable.truth, scalarTruth, Except.map,
          one, two, Ne.symm castOne, Ne.symm castTwo]
  by_cases allowed : n ≠ 1 ∧ n ≠ 2
  · have reduced : decide (accepted n) = decide (ProjectEulerStatements.P34.digitFactSum n = n) := by
      simp [accepted, allowed.1, allowed.2]
    rw [reduced]
    refine ⟨middle ++ [.list (digits n)], ?_⟩
    apply Evaluates.boolean_next (flag := true) (by simpa [allowed] using first) rfl rfl
    apply Evaluates.boolean_last
      (value := .scalar (.bool (decide (ProjectEulerStatements.P34.digitFactSum n = n))))
    · apply Evaluates.compare
        (Evaluates.call (.cons (Evaluates.lookup getN) .nil) (digit_fact_sum.result n middle))
        (Evaluates.lookup getN)
      simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    · rfl
  · have rejected : decide (accepted n) = false := by
      simp only [accepted, ← and_assoc, allowed, false_and, decide_false]
    rw [rejected]
    exact ⟨middle, Evaluates.boolean_stop (flag := false) (by simpa [allowed] using first) rfl rfl⟩

private def totalFrom (first count total : Nat) : Nat :=
  (List.range' first count).foldl (fun acc n => if accepted n then acc + n else acc) total

private theorem naive.loop (count first total : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getTotal : env sumAccumulator = some (number total)) :
    ∃ finalHeap, BlockReturns program env
      [.rangeStepLoop "n" first (first + count) 1 body [], .return (.name sumAccumulator)]
      heap (number (totalFrom first count total)) finalHeap := by
  induction count generalizing first total heap env with
  | zero =>
      refine ⟨heap, ?_⟩
      apply BlockReturns.range_done (by simp [Calls.rangeContinues])
      exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let boundEnv := setLocal env "n" (number first)
      obtain ⟨middle, tested⟩ := test_result first heap boundEnv (by simp [boundEnv, setLocal])
      by_cases yes : accepted first
      · let nextEnv := setLocal boundEnv sumAccumulator (number (total + first))
        obtain ⟨finalHeap, continued⟩ := ih (first + 1) (total + first) middle nextEnv
          (by simp [nextEnv, setLocal])
        refine ⟨finalHeap, ?_⟩
        apply BlockReturns.range_step (by simp [Calls.rangeContinues])
        apply BlockReturns.branch (flag := true) (by simpa [yes] using tested) rfl
        apply BlockReturns.assign (value := number (total + first)) (middle := middle)
        · apply Evaluates.binary (av := number total) (bv := number first)
            (Evaluates.lookup (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal))
            (Evaluates.lookup (by simp [setLocal]))
          simp [Mutable.binary, scalarBinary, number]
        · rw [totalFrom, List.range'_succ, List.foldl_cons, if_pos yes]
          simpa [body, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt, totalFrom, nextEnv, boundEnv,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm] using continued
      · obtain ⟨finalHeap, continued⟩ := ih (first + 1) total middle boundEnv
          (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal)
        refine ⟨finalHeap, ?_⟩
        apply BlockReturns.range_step (by simp [Calls.rangeContinues])
        apply BlockReturns.branch (flag := false) (by simpa [yes] using tested) rfl
        simpa [body, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
          Calls.loopControlStmt, totalFrom, List.range'_succ, List.foldl_cons, yes, boundEnv,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm] using continued

private theorem totalFrom_naive (limit : Nat) :
    totalFrom 0 (limit + 1) 0 = ProjectEulerStatements.P34.naive limit := by
  have same : (fun acc n => if accepted n then acc + n else acc) =
      (fun acc n => if n = 1 ∨ n = 2 then acc
        else if ProjectEulerStatements.P34.digitFactSum n = n then acc + n else acc) := by
    funext acc n
    by_cases one : n = 1 <;> by_cases two : n = 2 <;>
      by_cases equal : ProjectEulerStatements.P34.digitFactSum n = n <;>
      simp [accepted, one, two, equal]
  simp only [totalFrom, same, ProjectEulerStatements.P34.naive,
    ProjectEulerStatements.P34.sumCurious, List.range_eq_range']

theorem naive.result (limit : Nat) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive" [number limit] heap
      (number (ProjectEulerStatements.P34.naive limit)) finalHeap := by
  let env := functionEnv [⟨"limit", some (.name "int"), none⟩]
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit] []
  let summed := setLocal (comprehensionEnv env
    [("n", .call (.name "range") [.binOp (.name "limit") .add (.constant (.int 1))], [test])])
    sumAccumulator (number 0)
  obtain ⟨finalHeap, loop⟩ := naive.loop (limit + 1) 0 0 heap summed rfl
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range
    (.cons (Evaluates.binary (av := number limit) (bv := number 1)
      (value := number (limit + 1)) (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup rfl) Evaluates.constant
      (by simp [Mutable.binary, scalarBinary, number])) .nil)
    rfl Evaluates.constant rfl
  simpa only [Nat.zero_add, Nat.cast_add, Nat.cast_zero, Nat.cast_one, Int.zero_add, totalFrom_naive] using loop

theorem naive.«Returns» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P34Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Returns := by
  have nonnegative : 0 ≤ limit := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift limit to Nat using nonnegative
  obtain ⟨_, returned⟩ := naive.result limit []
  exact returned.scalar_returns

theorem naive.«Supported» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P34Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Supported :=
  (naive.«Returns» limit condition).supported

theorem naive_default.result (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive_default" [] heap
      (number (ProjectEulerStatements.P34.naive 2540160)) finalHeap := by
  obtain ⟨finalHeap, returned⟩ := naive.result 2540160 heap
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.call (.cons Evaluates.constant .nil) returned)

theorem naive_default.«Returns» : (HeapCalls.scalarFunction program "naive_default" []).Returns := by
  obtain ⟨_, returned⟩ := naive_default.result []
  exact ReturnsValue.scalar_returns (values := []) returned

theorem naive_default.«Supported» : (HeapCalls.scalarFunction program "naive_default" []).Supported :=
  naive_default.«Returns».supported

end data.«project-euler-statements».data.py.project_euler_statements.p34
