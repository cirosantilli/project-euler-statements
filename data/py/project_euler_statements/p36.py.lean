import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p36.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.SumCalls
import ProjectEulerStatements.Lib.DoublePalindromes
import Mathlib.Data.List.Range

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p36
open FormalSW.PyAst HeapCalls
private abbrev program := P36Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev digitValues (b n : Nat) : List Mutable.Value := (Nat.digits b n).map number
private abbrev palindromeHeap (b n : Nat) : Mutable.Heap :=
  [.list (digitValues b n), .list (digitValues b n).reverse]

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 4 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["is_palindrome_base", "is_double_palindrome", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

/-- List equality compares the original digits with the fresh reversed copy. -/
private theorem palindrome_test (b n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getDigits : env "ds" = some (.ref heap.length)) :
    Evaluates program env (.compare (.name "ds") [(.eq, .reversedList (.name "ds"))])
      (heap ++ [.list (digitValues b n)])
      (.scalar (.bool (ProjectEulerStatements.P36.isPalindromeBase b n)))
      (heap ++ [.list (digitValues b n)] ++ [.list (digitValues b n).reverse]) := by
  apply Evaluates.compare
    (Evaluates.lookup getDigits)
    (Evaluates.reversed_list (items := digitValues b n) (Evaluates.lookup getDigits) (by simp))
  have result := HeapCalls.compare_int_lists
    ((Nat.digits b n).map (fun (d : Nat) => (d : Int)))
    (((Nat.digits b n).reverse).map (fun (d : Nat) => (d : Int)))
    (heap := heap ++ [.list (digitValues b n)] ++ [.list (digitValues b n).reverse])
    (a := heap.length) (b := (heap ++ [Mutable.Object.list (digitValues b n)]).length)
    (by simp [digitValues, number, List.map_map])
    (by simp [digitValues, number, List.map_map, List.map_reverse])
  have injective : Function.Injective (List.map (fun d : Nat => (d : Int))) :=
    List.map_injective_iff.mpr Nat.cast_injective
  simpa only [ProjectEulerStatements.P36.isPalindromeBase, injective.eq_iff] using result

theorem is_palindrome_base.result (b n : Nat) (base : 2 ≤ b) (heap : Mutable.Heap) :
    ReturnsValue program "is_palindrome_base" [number b, number n] heap
      (.scalar (.bool (ProjectEulerStatements.P36.isPalindromeBase b n)))
      (heap ++ palindromeHeap b n) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign
    (Evaluates.call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil))
      ((common.digits_le.result n b (by omega) heap).extend common_extension))
  apply BlockReturns.return_value
  simpa only [palindromeHeap, List.append_assoc, List.singleton_append] using
    palindrome_test b n heap _ (by simp [setLocal])

/-- The binary test runs only after the decimal test succeeds. -/
theorem is_double_palindrome.result (n : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "is_double_palindrome" [number n] heap
      (.scalar (.bool (ProjectEulerStatements.P36.isDoublePalindrome n))) (heap ++ extra) := by
  let args := ((findFunctionIn program.body "is_double_palindrome").getD ([], [])).1
  let code := ((findFunctionIn program.body "is_double_palindrome").getD ([], [])).2
  let env := functionEnv args code [number n] []
  have decimal : Evaluates program env (.call (.name "is_palindrome_base") [.constant (.int 10), .name "n"])
      heap (.scalar (.bool (ProjectEulerStatements.P36.isPalindromeBase 10 n))) (heap ++ palindromeHeap 10 n) :=
    Evaluates.call (.cons Evaluates.constant (.cons (Evaluates.lookup rfl) .nil))
      (is_palindrome_base.result 10 n (by decide) heap)
  cases accepted : ProjectEulerStatements.P36.isPalindromeBase 10 n with
  | false =>
      refine ⟨palindromeHeap 10 n, ?_⟩
      apply BlockReturns.function rfl rfl
      apply BlockReturns.return_value
      simp only [ProjectEulerStatements.P36.isDoublePalindrome, accepted, Bool.false_and]
      exact Evaluates.boolean_stop (flag := false) (by simpa only [accepted] using decimal) rfl rfl
  | true =>
      refine ⟨palindromeHeap 10 n ++ palindromeHeap 2 n, ?_⟩
      apply BlockReturns.function rfl rfl
      apply BlockReturns.return_value
      simp only [ProjectEulerStatements.P36.isDoublePalindrome, accepted, Bool.true_and]
      apply Evaluates.boolean_next (flag := true) (by simpa only [accepted] using decimal) rfl rfl
      apply Evaluates.boolean_last (value := .scalar (.bool (ProjectEulerStatements.P36.isPalindromeBase 2 n)))
      · have binary : Evaluates program env
            (.call (.name "is_palindrome_base") [.constant (.int 2), .name "n"])
            (heap ++ palindromeHeap 10 n) (.scalar (.bool (ProjectEulerStatements.P36.isPalindromeBase 2 n)))
            ((heap ++ palindromeHeap 10 n) ++ palindromeHeap 2 n) :=
          Evaluates.call (.cons Evaluates.constant (.cons (Evaluates.lookup rfl) .nil))
            (is_palindrome_base.result 2 n (by decide) (heap ++ palindromeHeap 10 n))
        simpa only [List.append_assoc] using binary
      · rfl

private abbrev test : Expr := .call (.name "is_double_palindrome") [.name "n"]
private abbrev body : List Stmt := comprehensionFilters [test] (sumBody (.name "n") [])
private def totalFrom (first count total : Nat) : Nat :=
  (List.range' first count).foldl
    (fun acc n => if ProjectEulerStatements.P36.isDoublePalindrome n then acc + n else acc) total

/-- Every tested value is visited in ascending order; all allocations extend the heap. -/
private theorem naive.loop (count first total : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getTotal : env sumAccumulator = some (number total)) :
    ∃ extra, BlockReturns program env
      [.rangeStepLoop "n" first (first + count) 1 body [], .return (.name sumAccumulator)]
      heap (number (totalFrom first count total)) (heap ++ extra) := by
  induction count generalizing first total heap env with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues])
      exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let boundEnv := setLocal env "n" (number first)
      obtain ⟨allocated, predicate⟩ := is_double_palindrome.result first heap
      have tested : Evaluates program boundEnv test heap
          (.scalar (.bool (ProjectEulerStatements.P36.isDoublePalindrome first))) (heap ++ allocated) :=
        Evaluates.call (.cons (Evaluates.lookup (by simp [boundEnv, setLocal])) .nil) predicate
      cases yes : ProjectEulerStatements.P36.isDoublePalindrome first with
      | true =>
          let nextEnv := setLocal boundEnv sumAccumulator (number (total + first))
          obtain ⟨rest, continued⟩ := ih (first + 1) (total + first) (heap ++ allocated) nextEnv
            (by simp [nextEnv, setLocal])
          refine ⟨allocated ++ rest, ?_⟩
          apply BlockReturns.range_step (by simp [Calls.rangeContinues])
          apply BlockReturns.branch (flag := true) (by simpa only [yes] using tested) rfl
          apply BlockReturns.assign (value := number (total + first)) (middle := heap ++ allocated)
          · apply Evaluates.binary (av := number total) (bv := number first)
              (Evaluates.lookup (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal))
              (Evaluates.lookup (by simp [setLocal]))
            simp [Mutable.binary, scalarBinary, number]
          · simpa [body, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
              Calls.loopControlStmt, totalFrom, List.range'_succ, List.foldl_cons, yes, nextEnv, boundEnv,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm,
              List.append_assoc] using continued
      | false =>
          obtain ⟨rest, continued⟩ := ih (first + 1) total (heap ++ allocated) boundEnv
            (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal)
          refine ⟨allocated ++ rest, ?_⟩
          apply BlockReturns.range_step (by simp [Calls.rangeContinues])
          apply BlockReturns.branch (flag := false) (by simpa only [yes] using tested) rfl
          simpa [body, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt, totalFrom, List.range'_succ, List.foldl_cons, yes, boundEnv,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm,
            List.append_assoc] using continued

private theorem totalFrom_naive (limit : Nat) :
    totalFrom 0 limit 0 = ProjectEulerStatements.P36.naive limit := by
  rw [ProjectEulerStatements.DoublePalindromes.naive_fold]
  simp only [totalFrom, List.range_eq_range']

theorem naive.result (limit : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive" [number limit] heap
      (number (ProjectEulerStatements.P36.naive limit)) (heap ++ extra) := by
  let env := functionEnv [⟨"limit", some (.name "int"), none⟩]
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit] []
  let summed := setLocal (comprehensionEnv env
    [("n", .call (.name "range") [.name "limit"], [test])]) sumAccumulator (number 0)
  obtain ⟨extra, loop⟩ := naive.loop limit 0 0 heap summed rfl
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range (values := [number limit]) (middle := heap)
    (.cons (Evaluates.lookup rfl) .nil) rfl Evaluates.constant rfl
  simpa only [Nat.zero_add, Nat.cast_zero, Int.zero_add, totalFrom_naive] using loop

theorem naive.«Returns» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P36Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Returns := by
  have nonnegative : 0 ≤ limit := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift limit to Nat using nonnegative
  obtain ⟨_, returned⟩ := naive.result limit []
  exact returned.scalar_returns

theorem naive.«Supported» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P36Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Supported :=
  (naive.«Returns» limit condition).supported

end data.«project-euler-statements».data.py.project_euler_statements.p36
