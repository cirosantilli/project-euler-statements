import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p49.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.HeapCalls
import ProjectEulerSolutions.Lib.PrimePermutations
import ProjectEulerSolutions.Lib.HeapCollection

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p49
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.PrimePermutations
private abbrev program := P49Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private def numbers (values : List Int) : List Mutable.Value := values.map number

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 6++CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["digits_sorted", "is_permutation", "seq_from", "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private def digitObjects (n : Nat) : Mutable.Heap :=
  [.list (numbers (integerDigits n)), .list (numbers (sortedDigits n))]

namespace digits_sorted
/-- The source allocates its little-endian digits and a fresh sorted result, preserving every prior object. -/
theorem result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "digits_sorted" [number n] heap (.ref (heap.length+1)) (heap++digitObjects n) := by
  let middle := heap++[Mutable.Object.list (numbers (integerDigits n))]
  have converted : ReturnsValue program "digits_le" [number n] heap (.ref heap.length) middle := by
    simpa only [middle, numbers, integerDigits, List.map_map, Function.comp_def] using
      (common.digits_le.decimal n heap).extend common_extension
  have sorted := primitive_sorted_list middle heap.length ((integerDigits n).map Constant.int)
    ((sortedDigits n).map Constant.int)
    (by simp [middle, numbers, number, List.map_map]) (ScalarSort.sort_ints (integerDigits n))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin (.cons (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) converted) .nil)
  simpa [middle, digitObjects, numbers, number, List.map_map, List.append_assoc] using sorted

theorem «Returns» (n : Int)
    (condition : Calls.Condition program (fun name => if name="n" then some (.int n) else none) P49Ast.requires_digits_sorted_0) :
    (HeapCalls.call program "digits_sorted" [number n] []).Returns := by
  have nonnegative : 0≤n := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift n to Nat using nonnegative
  exact (result n []).returns

theorem «Supported» (n : Int)
    (condition : Calls.Condition program (fun name => if name="n" then some (.int n) else none) P49Ast.requires_digits_sorted_0) :
    (HeapCalls.call program "digits_sorted" [number n] []).Supported := («Returns» n condition).supported
end digits_sorted

namespace is_permutation
/-- Both sorted lists are compared by contents after all argument allocations have occurred. -/
theorem result (a b : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "is_permutation" [number a, number b] heap
      (flag (ProjectEulerStatements.P49.isPermutation a b)) (heap++digitObjects a++digitObjects b) := by
  rw [← permutation_statement]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.compare (av := .ref (heap.length+1)) (bv := .ref ((heap++digitObjects a).length+1))
    (middle := heap++digitObjects a) (afterRight := heap++digitObjects a++digitObjects b)
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (digits_sorted.result a heap)
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (digits_sorted.result b (heap++digitObjects a))
  · apply compare_int_lists (sortedDigits a) (sortedDigits b)
    · simp [digitObjects, numbers, List.append_assoc]
    · simp [digitObjects, numbers, List.append_assoc, Nat.add_assoc]

private abbrev inputEnv (a b : Int) : ScalarEnv :=
  fun name => if name="a" then some (.int a) else if name="b" then some (.int b) else none

private theorem condition_result (a b : Int) :
    Calls.Evaluates program (inputEnv a b) P49Ast.requires_is_permutation_0 (.bool (decide (0≤a ∧ 0≤b))) := by
  have left : Calls.Evaluates program (inputEnv a b) (.compare (.name "a") [(.gtE, .constant (.int 0))])
      (.bool (decide (0≤a))) := Calls.Evaluates.compare (Calls.Evaluates.lookup rfl) Calls.Evaluates.constant rfl
  have right : Calls.Evaluates program (inputEnv a b) (.compare (.name "b") [(.gtE, .constant (.int 0))])
      (.bool (decide (0≤b))) := Calls.Evaluates.compare (Calls.Evaluates.lookup rfl) Calls.Evaluates.constant rfl
  by_cases lower : 0≤a
  · apply Calls.Evaluates.boolean_continue (by simpa only [lower, decide_true] using left) rfl
    apply Calls.Evaluates.boolean_last
    simpa only [lower, true_and] using right
  · simp only [lower, false_and, decide_false]
    exact Calls.Evaluates.boolean_stop (by simpa only [lower, decide_false] using left) rfl

theorem «Returns» (a b : Int) (condition : Calls.Condition program (inputEnv a b) P49Ast.requires_is_permutation_0) :
    (HeapCalls.scalarFunction program "is_permutation" [.int a, .int b]).Returns := by
  have bounds : 0≤a ∧ 0≤b := by simpa using (condition_result a b).condition_iff.mp condition
  lift a to Nat using bounds.1
  lift b to Nat using bounds.2
  exact (result a b []).scalar_returns

theorem «Supported» (a b : Int) (condition : Calls.Condition program (inputEnv a b) P49Ast.requires_is_permutation_0) :
    (HeapCalls.scalarFunction program "is_permutation" [.int a, .int b]).Supported := («Returns» a b condition).supported
end is_permutation

namespace seq_from
private def expression : Expr := .binOp (.name "a") .add (.binOp (.name "i") .mult (.name "d"))

private theorem loop (a d : Int) (first count stop : Nat) (length : first+count=stop)
    (base : Mutable.Heap) (values : List Int) (env : HeapCalls.Env)
    (getA : env "a"=some (number a)) (getD : env "d"=some (number d)) :
    ∃ finalEnv, BlockContinues program env
      [.rangeStepLoop "i" first stop 1 [.comprehensionAppend base.length expression] []]
      (ProjectEulerSolutions.HeapCollection.working base (numbers values) []) finalEnv
      (ProjectEulerSolutions.HeapCollection.working base
        (numbers (values++(List.range' first count).map (fun (i : Nat) => a+(i : Int)*d))) []) := by
  induction count generalizing first values env with
  | zero =>
      refine ⟨env, ?_⟩
      simp only [List.range'_zero, List.map_nil, List.append_nil]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  | succ count ih =>
      let bound := setLocal env "i" (number first)
      have boundA : bound "a"=some (number a) := by simpa [bound, setLocal] using getA
      have boundD : bound "d"=some (number d) := by simpa [bound, setLocal] using getD
      have evaluated : Evaluates program bound expression
          (ProjectEulerSolutions.HeapCollection.working base (numbers values) []) (number (a+(first : Int)*d))
          (ProjectEulerSolutions.HeapCollection.working base (numbers values) []) := by
        exact Evaluates.binary (av := number a) (bv := number ((first : Int)*d))
          (Evaluates.lookup boundA)
          (Evaluates.binary (av := number first) (bv := number d) (Evaluates.lookup rfl) (Evaluates.lookup boundD) rfl) rfl
      have emitted := ProjectEulerSolutions.HeapCollection.emit base (numbers values) [] [] (number (a+(first : Int)*d))
        (by simpa only [List.append_nil] using evaluated)
      obtain ⟨finalEnv, rest⟩ := ih (first+1) (by omega) (values++[a+(first : Int)*d]) bound boundA boundD
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      have firstStep : BlockContinues program bound [.comprehensionAppend base.length expression]
          (ProjectEulerSolutions.HeapCollection.working base (numbers values) []) bound
          (ProjectEulerSolutions.HeapCollection.working base (numbers (values++[a+(first : Int)*d])) []) := by
        simpa only [numbers, List.map_append, List.map_cons, List.map_nil, List.append_nil] using emitted
      simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        Bool.false_or, Bool.false_eq_true, if_false, List.range'_succ, List.map_cons,
        List.append_assoc, List.singleton_append, Int.natCast_add, Int.natCast_one] using firstStep.append rest

/-- The source comprehension terminates for every signed start, difference and length. -/
theorem result (a d length : Int) (heap : Mutable.Heap) :
    ReturnsValue program "seq_from" [number a, number d, number length] heap (.ref heap.length)
      (heap++[.list (numbers (progression a d length.toNat))]) := by
  let initial := functionEnv ((findFunctionIn program.body "seq_from").getD ([], [])).1
    ((findFunctionIn program.body "seq_from").getD ([], [])).2 [number a, number d, number length] []
  let inner := comprehensionEnv initial [("i", .call (.name "range") [.name "length"], [])]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  by_cases below : length<0
  · have empty : length.toNat=0 := Int.toNat_eq_zero.mpr (by omega)
    simp only [empty, progression, List.range_zero, List.map_nil, numbers]
    apply Evaluates.list_comp_range (.cons (Evaluates.lookup rfl) .nil) rfl
    exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  · lift length to Nat using (by omega : 0≤length)
    obtain ⟨finalEnv, run⟩ := loop a d 0 length length (by omega) heap [] inner rfl rfl
    apply Evaluates.list_comp_range (finalEnv := finalEnv) (.cons (Evaluates.lookup rfl) .nil) rfl
    simpa only [ProjectEulerSolutions.HeapCollection.working, numbers, List.map_nil, List.nil_append,
      progression, Int.toNat_natCast, List.range_eq_range'] using run

theorem «Returns» (a d length : Int) : (HeapCalls.call program "seq_from" [number a, number d, number length] []).Returns :=
  (result a d length []).returns

theorem «Supported» (a d length : Int) : (HeapCalls.call program "seq_from" [number a, number d, number length] []).Supported :=
  («Returns» a d length).supported
end seq_from

end data.«project-euler-statements».data.py.project_euler_statements.p49
