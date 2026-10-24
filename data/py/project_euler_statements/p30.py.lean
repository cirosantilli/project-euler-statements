import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p30.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.SumCalls
import ProjectEulerStatements.P30
import Mathlib.Data.List.Range

namespace data.«project-euler-statements».data.py.project_euler_statements.p30
open FormalSW.PyAst HeapCalls
private abbrev program := P30Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev digits (n : Nat) : List Mutable.Value := (Nat.digits 10 n).map number

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 4 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["digit_power_sum", "limit", "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private abbrev power : Expr := .binOp (.name "d") .pow (.name "p")

/-- Captured parameters survive both the sequence binding and accumulator update. -/
private theorem digit_loop (p : Nat) (values remaining : List Nat) (position total : Nat)
    (heap : Mutable.Heap) (source : SequenceSource) (env : HeapCalls.Env)
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok (values.map number), heap))
    (suffix : values.drop position = remaining)
    (getP : env "p" = some (number p))
    (getTotal : env sumAccumulator = some (number total)) :
    BlockReturns program env
      [.sequenceStepLoop "d" source position (sumBody power []) [], .return (.name sumAccumulator)]
      heap (number (remaining.foldl (fun acc d => acc + d ^ p) total)) heap := by
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
      apply BlockReturns.assign (value := number (total + head ^ p)) (middle := heap)
      · apply Evaluates.binary (av := number total) (bv := number (head ^ p)) (middle := heap) (afterRight := heap)
          (Evaluates.lookup (by simpa [setLocal, sumAccumulator] using getTotal))
        · apply Evaluates.binary (av := number head) (bv := number p) (middle := heap) (afterRight := heap)
            (Evaluates.lookup (by simp [setLocal]))
            (Evaluates.lookup (by simpa [setLocal] using getP))
          simp [Mutable.binary, scalarBinary, number, show ¬ (p : Int) < 0 by omega]
        · simp [Mutable.binary, scalarBinary, number]
      · change BlockReturns program _
          [.sequenceStepLoop "d" source (position + 1) (sumBody power []) [],
            .return (.name sumAccumulator)] heap _ heap
        apply ih
        · simp [List.drop_add_one_eq_tail_drop, suffix]
        · simpa [setLocal, sumAccumulator] using getP
        · simp [setLocal]

theorem digit_power_sum.result (p n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "digit_power_sum" [number p, number n] heap
      (number (ProjectEulerStatements.P30.digitPowerSum p n)) (heap ++ [.list (digits n)]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_sequence (items := digits n)
    (by intro expressions; simp)
    (Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
      ((common.digits_le.decimal n heap).extend common_extension))
  · simp [Mutable.sequence, digits]
  · exact Evaluates.constant
  · rfl
  · apply digit_loop p (Nat.digits 10 n) (Nat.digits 10 n) 0 0
    · simp [Mutable.sequence, sequenceValue, sequenceSource]
    · rfl
    · rfl
    · rfl

theorem limit.result (p : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "limit" [number p] heap
      (number (ProjectEulerStatements.P30.limit p)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := number (p + 2)) (bv := number (9 ^ p)) (middle := heap) (afterRight := heap)
  · apply Evaluates.binary (av := number p) (bv := number 2) (middle := heap) (afterRight := heap)
      (Evaluates.lookup rfl) Evaluates.constant
    simp [Mutable.binary, scalarBinary, number]
  · apply Evaluates.binary (av := number 9) (bv := number p) (middle := heap) (afterRight := heap)
      Evaluates.constant (Evaluates.lookup rfl)
    simp [Mutable.binary, scalarBinary, number, show ¬ (p : Int) < 0 by omega]
  · simp [Mutable.binary, scalarBinary, number, ProjectEulerStatements.P30.limit]

private abbrev accepted (p n : Nat) : Prop := n ≠ 1 ∧ ProjectEulerStatements.P30.digitPowerSum p n = n
private abbrev test : Expr := .boolOp .and
  [.compare (.name "n") [(.notEq, .constant (.int 1))],
   .compare (.call (.name "digit_power_sum") [.name "p", .name "n"]) [(.eq, .name "n")]]
private abbrev body : List Stmt := comprehensionFilters [test] (sumBody (.name "n") [])

private theorem test_result (p n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getP : env "p" = some (number p)) (getN : env "n" = some (number n)) :
    ∃ finalHeap, Evaluates program env test heap (.scalar (.bool (decide (accepted p n)))) finalHeap := by
  have first : Evaluates program env (.compare (.name "n") [(.notEq, .constant (.int 1))]) heap
      (.scalar (.bool (decide (n ≠ 1)))) heap := by
    apply Evaluates.compare (Evaluates.lookup getN) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  by_cases one : n = 1
  · have rejected : decide (accepted p n) = false := by simp [accepted, one]
    rw [rejected]
    exact ⟨heap, Evaluates.boolean_stop (flag := false) (by simpa [one] using first) rfl rfl⟩
  · have reduced : decide (accepted p n) = decide (ProjectEulerStatements.P30.digitPowerSum p n = n) := by
      simp [accepted, one]
    rw [reduced]
    refine ⟨heap ++ [.list (digits n)], ?_⟩
    apply Evaluates.boolean_next (flag := true) (by simpa [one] using first) rfl rfl
    apply Evaluates.boolean_last
      (value := .scalar (.bool (decide (ProjectEulerStatements.P30.digitPowerSum p n = n))))
    · apply Evaluates.compare
        (Evaluates.call (.cons (Evaluates.lookup getP) (.cons (Evaluates.lookup getN) .nil))
          (digit_power_sum.result p n heap)) (Evaluates.lookup getN)
      simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    · rfl

private def totalFrom (p first count total : Nat) : Nat :=
  (List.range' first count).foldl (fun acc n => if accepted p n then acc + n else acc) total

private theorem naive.loop (p count first total : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getP : env "p" = some (number p))
    (getTotal : env sumAccumulator = some (number total)) :
    ∃ finalHeap, BlockReturns program env
      [.rangeStepLoop "n" first (first + count) 1 body [], .return (.name sumAccumulator)]
      heap (number (totalFrom p first count total)) finalHeap := by
  induction count generalizing first total heap env with
  | zero =>
      refine ⟨heap, ?_⟩
      apply BlockReturns.range_done (by simp [Calls.rangeContinues])
      exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let boundEnv := setLocal env "n" (number first)
      have keptP : boundEnv "p" = some (number p) := by simpa [boundEnv, setLocal] using getP
      obtain ⟨middle, tested⟩ := test_result p first heap boundEnv keptP (by simp [boundEnv, setLocal])
      by_cases yes : accepted p first
      · let nextEnv := setLocal boundEnv sumAccumulator (number (total + first))
        obtain ⟨finalHeap, continued⟩ := ih (first + 1) (total + first) middle nextEnv
          (by simpa [nextEnv, setLocal, sumAccumulator] using keptP) (by simp [nextEnv, setLocal])
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
      · obtain ⟨finalHeap, continued⟩ := ih (first + 1) total middle boundEnv keptP
          (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal)
        refine ⟨finalHeap, ?_⟩
        apply BlockReturns.range_step (by simp [Calls.rangeContinues])
        apply BlockReturns.branch (flag := false) (by simpa [yes] using tested) rfl
        simpa [body, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
          Calls.loopControlStmt, totalFrom, List.range'_succ, List.foldl_cons, yes, boundEnv,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm] using continued

private theorem totalFrom_naive (p : Nat) :
    totalFrom p 0 (ProjectEulerStatements.P30.limit p + 1) 0 = ProjectEulerStatements.P30.naive p := by
  have same : (fun acc n => if accepted p n then acc + n else acc) =
      (fun acc n => if n = 1 then acc else if ProjectEulerStatements.P30.digitPowerSum p n = n then acc + n else acc) := by
    funext acc n
    by_cases one : n = 1 <;> by_cases equal : ProjectEulerStatements.P30.digitPowerSum p n = n <;>
      simp [accepted, one, equal]
  simp only [totalFrom, same, ProjectEulerStatements.P30.naive,
    ProjectEulerStatements.P30.sumPowerDigits, List.range_eq_range']

theorem naive.result (p : Nat) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive" [number p] heap
      (number (ProjectEulerStatements.P30.naive p)) finalHeap := by
  let env := functionEnv [⟨"p", some (.name "int"), none⟩]
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number p] []
  let summed := setLocal (comprehensionEnv env
    [("n", .call (.name "range") [.binOp (.call (.name "limit") [.name "p"]) .add (.constant (.int 1))], [test])])
    sumAccumulator (number 0)
  obtain ⟨finalHeap, loop⟩ := naive.loop p (ProjectEulerStatements.P30.limit p + 1) 0 0 heap summed rfl rfl
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range
    (.cons (Evaluates.binary (av := number (ProjectEulerStatements.P30.limit p)) (bv := number 1)
      (value := number (ProjectEulerStatements.P30.limit p + 1)) (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (limit.result p heap)) Evaluates.constant
      (by simp [Mutable.binary, scalarBinary, number])) .nil)
    rfl Evaluates.constant rfl
  simpa only [Nat.zero_add, Nat.cast_add, Nat.cast_zero, Nat.cast_one, Int.zero_add, totalFrom_naive] using loop

theorem naive.«Returns» (p : Int)
    (condition : Calls.Condition program (fun name => if name = "p" then some (.int p) else none)
      P30Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int p]).Returns := by
  have nonnegative : 0 ≤ p := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift p to Nat using nonnegative
  obtain ⟨_, returned⟩ := naive.result p []
  exact returned.scalar_returns

theorem naive.«Supported» (p : Int)
    (condition : Calls.Condition program (fun name => if name = "p" then some (.int p) else none)
      P30Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int p]).Supported :=
  (naive.«Returns» p condition).supported

theorem naive_default.result (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive_default" [] heap
      (number (ProjectEulerStatements.P30.naive 5)) finalHeap := by
  obtain ⟨finalHeap, returned⟩ := naive.result 5 heap
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.call (.cons Evaluates.constant .nil) returned)

theorem naive_default.«Returns» : (HeapCalls.scalarFunction program "naive_default" []).Returns := by
  obtain ⟨_, returned⟩ := naive_default.result []
  exact ReturnsValue.scalar_returns (values := []) returned

theorem naive_default.«Supported» : (HeapCalls.scalarFunction program "naive_default" []).Supported :=
  naive_default.«Returns».supported

end data.«project-euler-statements».data.py.project_euler_statements.p30
