import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p25.py.ast»
import lang.py.FormalSW.MemoCallRules
import Mathlib.Data.Nat.Fib.Basic
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerStatements.Lib.FibonacciDigits
import lang.py.FormalSW.MemoHeapCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p25
open FormalSW.PyAst FormalSW.PyAst.MemoCalls
private abbrev program := P25Ast.module

/-- Every cached entry contains the exact Fibonacci value at its nonnegative key. -/
def fibSpec (key : Key) (value : Constant) : Prop :=
  ∃ n : Nat, key = ⟨"fib", [n]⟩ ∧ value = .int (Nat.fib n)

private theorem fibSpec_unique (n : Nat) (value : Constant) (correct : fibSpec ⟨"fib", [n]⟩ value) :
    value = .int (Nat.fib n) := by
  obtain ⟨index, same, rfl⟩ := correct
  have equalInt : (n : Int) = index := by simpa [Key.mk.injEq] using same
  have equal : n = index := by omega
  simp [equal]

/-- Cached and uncached calls satisfy the same recurrence, preserving all valid cache entries. -/
theorem fib.result (n : Nat) : ReturnsValue program ["fib"] fibSpec "fib" [.int n] (.int (Nat.fib n)) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      apply BlockReturns.memoized_function (values := [0]) (by simp) rfl rfl
      · apply BlockReturns.branch (value := .bool true)
          (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl)
        exact BlockReturns.return_value Evaluates.constant
      · exact ⟨0, rfl, rfl⟩
      · exact fun value => fibSpec_unique 0 value
  | one =>
      apply BlockReturns.memoized_function (values := [1]) (by simp) rfl rfl
      · apply BlockReturns.branch (value := .bool false)
          (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl)
        apply BlockReturns.branch (value := .bool true)
          (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl)
        exact BlockReturns.return_value Evaluates.constant
      · exact ⟨1, rfl, rfl⟩
      · exact fun value => fibSpec_unique 1 value
  | more n previous current =>
      apply BlockReturns.memoized_function (values := [n + 2]) (by simp) rfl rfl
      · apply BlockReturns.branch (value := .bool false)
          (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp]; omega))
        apply BlockReturns.branch (value := .bool false)
          (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp]; omega))
        apply BlockReturns.return_value
        apply Evaluates.binary (av := .int (Nat.fib (n + 1))) (bv := .int (Nat.fib n))
        · apply Evaluates.call (values := [.int (n + 1)])
          · exact .cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary]; omega)) .nil
          · exact current
        · apply Evaluates.call (values := [.int n])
          · exact .cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary])) .nil
          · exact previous
        · simp [scalarBinary, Nat.fib_add_two, Int.add_comm]
      · exact ⟨n + 2, rfl, rfl⟩
      · exact fun value => fibSpec_unique (n + 2) value

theorem fib.«Returns» (n : Int) (requires : Calls.Condition program
    (fun name => if name = "n" then some (.int n) else none) P25Ast.requires_fib_0) :
    (sourceFunction program "fib" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare requires rfl
  simpa [sourceFunction, Int.toNat_of_nonneg nonnegative] using (fib.result n.toNat).returns

theorem fib.«Supported» (n : Int) (requires : Calls.Condition program
    (fun name => if name = "n" then some (.int n) else none) P25Ast.requires_fib_0) :
    (sourceFunction program "fib" [.int n]).Supported := (fib.«Returns» n requires).supported


section HeapSearch
open MemoHeapCalls
open ProjectEulerStatements.FibonacciDigits

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  have extension : Calls.Extends { body := program.body.take 4 ++ CommonAst.module.body } CommonAst.module := by
    apply Calls.Extends.prepend
    · intro name member
      change name ∈ ["fib", "num_digits", "naive"] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    · intro name member
      change name ∈ ([] : List String) at member
      simp at member
  exact ⟨extension.functions, extension.libraries⟩

private theorem common_disjoint : CacheDisjoint program CommonAst.module := by
  intro name cached
  have same : name = "fib" := by
    change name ∈ ["fib"] at cached
    simpa using cached
  subst name
  decide

private abbrev digitValues (n : Nat) : List Mutable.Value :=
  (Nat.digits 10 n).map (fun (d : Nat) => .scalar (.int d))

private theorem fib_heap (n : Nat) (heap : Mutable.Heap) :
    MemoHeapCalls.ReturnsValue program fibSpec "fib" [.scalar (.int n)] heap
      (.scalar (.int (Nat.fib n))) heap :=
  MemoHeapCalls.ReturnsValue.memoized (by decide) (fib.result n)

theorem num_digits.result (n : Nat) (heap : Mutable.Heap) :
    MemoHeapCalls.ReturnsValue program fibSpec "num_digits" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P25.numDigits n))) (heap ++ [.list (digitValues n)]) := by
  apply MemoHeapCalls.BlockReturns.function (by decide) rfl rfl
  apply MemoHeapCalls.BlockReturns.return_value
  apply MemoHeapCalls.Evaluates.builtin
    (.cons (MemoHeapCalls.Evaluates.call (.cons (MemoHeapCalls.Evaluates.lookup rfl) .nil)
      (MemoHeapCalls.ReturnsValue.from_heap common_extension common_disjoint (common.digits_le.decimal n heap))) .nil)
  simp [HeapCalls.primitive, Mutable.length, digitValues, ProjectEulerStatements.P25.numDigits]

private def searchLoop : List Stmt :=
  (executableBody ((findFunctionIn program.body "naive").getD ([], [])).2).drop 1

private theorem search_result (digits index : Nat) (bound : index ≤ first digits)
    (env : Mutable.Env) (getN : env "n" = some (.scalar (.int digits)))
    (getI : env "i" = some (.scalar (.int index))) (heap : Mutable.Heap) :
    ∃ finalHeap, MemoHeapCalls.BlockReturns program fibSpec env searchLoop heap
      (.scalar (.int (first digits))) finalHeap := by
  induction measure : first digits - index using Nat.strong_induction_on generalizing index env heap with
  | h measure ih =>
      have evaluated : MemoHeapCalls.Evaluates program fibSpec env
          (.compare (.name "n") [(.ltE, .call (.name "num_digits") [.call (.name "fib") [.name "i"]])])
          heap (.scalar (.bool (decide (digits ≤ ProjectEulerStatements.P25.numDigits (Nat.fib index)))))
          (heap ++ [.list (digitValues (Nat.fib index))]) := by
        apply MemoHeapCalls.Evaluates.compare (MemoHeapCalls.Evaluates.lookup getN)
          (MemoHeapCalls.Evaluates.call (.cons
            (MemoHeapCalls.Evaluates.call (.cons (MemoHeapCalls.Evaluates.lookup getI) .nil) (fib_heap index heap)) .nil)
            (num_digits.result (Nat.fib index) heap))
        simp [HeapCalls.compare, scalarCompare, evalCmpOp]
      by_cases reached : digits ≤ ProjectEulerStatements.P25.numDigits (Nat.fib index)
      · have same : index = first digits := by
          have lower := Nat.find_min' (ProjectEulerStatements.P25.exists_fib_digits digits) reached
          change first digits ≤ index at lower
          omega
        refine ⟨heap ++ [.list (digitValues (Nat.fib index))], ?_⟩
        apply MemoHeapCalls.BlockReturns.while_loop MemoHeapCalls.Evaluates.constant rfl
        apply MemoHeapCalls.BlockReturns.branch (flag := true) (by simpa [reached] using evaluated) rfl
        apply MemoHeapCalls.BlockReturns.return_value
        exact MemoHeapCalls.Evaluates.lookup (by simpa [same] using getI)
      · have before : index < first digits := by
          have spec := first_spec digits
          by_contra no
          have same : index = first digits := by omega
          exact reached (same ▸ spec)
        obtain ⟨finalHeap, rest⟩ := ih (first digits - (index + 1)) (by omega) (index + 1) (by omega)
          (HeapCalls.setLocal env "i" (.scalar (.int (index + 1))))
          (by simpa [HeapCalls.setLocal] using getN) (by simp [HeapCalls.setLocal])
          (heap ++ [.list (digitValues (Nat.fib index))]) rfl
        refine ⟨finalHeap, ?_⟩
        apply MemoHeapCalls.BlockReturns.while_loop MemoHeapCalls.Evaluates.constant rfl
        apply MemoHeapCalls.BlockReturns.branch (flag := false) (by simpa [reached] using evaluated) rfl
        apply MemoHeapCalls.BlockReturns.augAssign (value := .scalar (.int (index + 1)))
          (afterOperation := heap ++ [.list (digitValues (Nat.fib index))]) getI MemoHeapCalls.Evaluates.constant
        · simp [HeapCalls.inplace, Mutable.binary, scalarBinary]
        · exact rest

/-- Every digit threshold is reached; list allocations and the shared Fibonacci cache are preserved. -/
theorem naive.result (digits : Nat) (heap : Mutable.Heap) :
    ∃ finalHeap, MemoHeapCalls.ReturnsValue program fibSpec "naive" [.scalar (.int digits)] heap
      (.scalar (.int (first digits))) finalHeap := by
  obtain ⟨finalHeap, run⟩ := search_result digits 0 (by omega)
    (HeapCalls.setLocal (HeapCalls.argumentEnv [{ name := "n", annotation := some (.name "int") }]
      [.scalar (.int digits)]) "i" (.scalar (.int 0))) rfl rfl heap
  refine ⟨finalHeap, ?_⟩
  apply MemoHeapCalls.BlockReturns.function (by decide) rfl rfl
  exact MemoHeapCalls.BlockReturns.assign MemoHeapCalls.Evaluates.constant run

end HeapSearch


theorem naive.«Returns» (digits : Int) (requires : Calls.Condition program
    (fun name => if name = "n" then some (.int digits) else none) P25Ast.requires_naive_0) :
    (MemoHeapCalls.scalarFunction program "naive" [.int digits]).Returns := by
  have nonnegative : 0 ≤ digits := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare requires rfl
  lift digits to Nat using nonnegative
  obtain ⟨heap, result⟩ := naive.result digits []
  exact MemoHeapCalls.ReturnsValue.scalar_returns result

theorem naive.«Supported» (digits : Int) (requires : Calls.Condition program
    (fun name => if name = "n" then some (.int digits) else none) P25Ast.requires_naive_0) :
    (MemoHeapCalls.scalarFunction program "naive" [.int digits]).Supported := (naive.«Returns» digits requires).supported

end data.«project-euler-statements».data.py.project_euler_statements.p25
