import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p52.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.HeapCalls
import ProjectEulerSolutions.Lib.PrimePermutations
import ProjectEulerSolutions.Lib.PermutedMultiples
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerSolutions.Lib.HeapTruthCollection

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p52
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.PrimePermutations
private abbrev program := P52Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private def numbers (values : List Int) : List Mutable.Value := values.map number

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 5++CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["digits_sorted", "same_digits", "has_permuted_multiples", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
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
    (condition : Calls.Condition program (fun name => if name="n" then some (.int n) else none) P52Ast.requires_digits_sorted_0) :
    (HeapCalls.call program "digits_sorted" [number n] []).Returns := by
  have nonnegative : 0≤n := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift n to Nat using nonnegative
  exact (result n []).returns

theorem «Supported» (n : Int)
    (condition : Calls.Condition program (fun name => if name="n" then some (.int n) else none) P52Ast.requires_digits_sorted_0) :
    (HeapCalls.call program "digits_sorted" [number n] []).Supported := («Returns» n condition).supported
end digits_sorted

namespace same_digits
/-- Both sorted lists are compared by contents after all argument allocations have occurred. -/
theorem result (a b : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "same_digits" [number a, number b] heap
      (flag (ProjectEulerSolutions.PermutedMultiples.same a b)) (heap++digitObjects a++digitObjects b) := by
  rw [← ProjectEulerSolutions.PermutedMultiples.sorted_same]
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
    Calls.Evaluates program (inputEnv a b) P52Ast.requires_same_digits_0 (.bool (decide (0≤a ∧ 0≤b))) := by
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

theorem «Returns» (a b : Int) (condition : Calls.Condition program (inputEnv a b) P52Ast.requires_same_digits_0) :
    (HeapCalls.scalarFunction program "same_digits" [.int a, .int b]).Returns := by
  have bounds : 0≤a ∧ 0≤b := by simpa using (condition_result a b).condition_iff.mp condition
  lift a to Nat using bounds.1
  lift b to Nat using bounds.2
  exact (result a b []).scalar_returns

theorem «Supported» (a b : Int) (condition : Calls.Condition program (inputEnv a b) P52Ast.requires_same_digits_0) :
    (HeapCalls.scalarFunction program "same_digits" [.int a, .int b]).Supported := («Returns» a b condition).supported
end same_digits

namespace has_permuted_multiples
private def element : Expr := .call (.name "same_digits")
  [.name "x", .binOp (.binOp (.name "i") .add (.constant (.int 2))) .mult (.name "x")]

private theorem checked (x i : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getX : env "x" = some (number x)) (getI : env "i" = some (number i)) :
    ∃ extra, Evaluates program env element heap
      (flag (ProjectEulerSolutions.PermutedMultiples.same x ((i+2)*x))) (heap ++ extra) := by
  refine ⟨digitObjects x ++ digitObjects ((i+2)*x), ?_⟩
  have returned := same_digits.result x ((i+2)*x) heap
  apply Evaluates.call (middle := heap) (values := [number x, number ((i+2)*x : Nat)])
  · refine .cons (Evaluates.lookup getX) (.cons ?_ .nil)
    apply Evaluates.binary (av := number (i+2 : Nat)) (bv := number x) (middle := heap) (afterRight := heap)
    · exact Evaluates.binary (Evaluates.lookup getI) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])
    · exact Evaluates.lookup getX
    · simp [Mutable.binary, scalarBinary, number]
  · simpa only [List.append_assoc] using returned

private theorem all_result (limit x : Nat) (supported : 2 ≤ limit) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number limit)) (getX : env "x" = some (number x)) :
    ∃ extra, Evaluates program env
      (.consumeGenerator (.builtinCall .all []) element
        [(.name "i", .call (.name "range") [.binOp (.name "n") .sub (.constant (.int 1))], [])])
      heap (flag ((List.range (limit-1)).all (fun i => ProjectEulerSolutions.PermutedMultiples.same x ((i+2)*x)))) (heap ++ extra) := by
  let captured := comprehensionTargetsEnv env
    [(.name "i", .call (.name "range") [.binOp (.name "n") .sub (.constant (.int 1))], [])]
  obtain ⟨extra, scanned⟩ := ProjectEulerSolutions.HeapTruthCollection.all_range_loop program "i" element
    (fun inner => inner "x" = some (number x)) (fun i => ProjectEulerSolutions.PermutedMultiples.same x ((i+2)*x))
    (by intro inner i valid; simpa [setLocal] using valid)
    (by intro heap inner i valid current; exact checked x i heap inner valid current)
    0 (limit-1) (limit-1) (by omega) captured heap (by simpa [captured, comprehensionTargetsEnv, targetLocals] using getX)
  refine ⟨extra, ?_⟩
  apply Evaluates.truth_generator_range (universal := true) (middle := heap) (values := [number (limit-1 : Nat)])
    (first := 0) (stop := ((limit-1 : Nat) : Int)) (stride := 1)
  · refine .cons ?_ .nil
    apply Evaluates.binary (Evaluates.lookup getN) Evaluates.constant
    have cast : ((limit-1 : Nat) : Int) = (limit : Int)-1 := by omega
    simp [Mutable.binary, scalarBinary, number, cast]
  · rfl
  · simpa only [captured, List.range_eq_range', comprehensionTargetName, comprehensionTargetBody,
      comprehensionFilters, comprehensionTargetsBody] using scanned

/-- The reference checks each requested multiple lazily and stops before later allocations on failure. -/
theorem result (limit : Int) (x : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "has_permuted_multiples" [number limit, number x] heap
      (flag (ProjectEulerSolutions.PermutedMultiples.accepts limit x)) (heap ++ extra) := by
  let entry := functionEnv ((findFunctionIn program.body "has_permuted_multiples").getD ([], [])).1
    ((findFunctionIn program.body "has_permuted_multiples").getD ([], [])).2 [number limit, number x] []
  have guard : Evaluates program entry (.compare (.name "n") [(.gtE, .constant (.int 2))])
      heap (flag (decide (2 ≤ limit))) heap :=
    Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant rfl
  by_cases supported : 2 ≤ limit
  · lift limit to Nat using (by omega : 0 ≤ limit)
    obtain ⟨extra, tested⟩ := all_result limit x (by omega) heap entry rfl rfl
    refine ⟨extra, ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    have natural : ((limit : Int)-1).toNat = limit-1 := by omega
    simp only [ProjectEulerSolutions.PermutedMultiples.accepts, supported, decide_true, Bool.true_and, natural]
    apply Evaluates.boolean_next (flag := true) (value := flag true) (middle := heap)
      (by simpa only [supported, decide_true] using guard) rfl rfl
    exact Evaluates.boolean_last tested rfl
  · refine ⟨[], ?_⟩
    simp only [List.append_nil, ProjectEulerSolutions.PermutedMultiples.accepts, supported, decide_false, Bool.false_and]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    exact Evaluates.boolean_stop (flag := false) (by simpa only [supported, decide_false] using guard) rfl rfl

theorem «Returns» (limit x : Int)
    (condition : Calls.Condition program (fun name => if name = "x" then some (.int x) else none) P52Ast.requires_has_permuted_multiples_0) :
    (HeapCalls.scalarFunction program "has_permuted_multiples" [.int limit, .int x]).Returns := by
  have nonnegative : 0 ≤ x := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift x to Nat using nonnegative
  obtain ⟨extra, returned⟩ := result limit x []
  exact returned.scalar_returns

theorem «Supported» (limit x : Int)
    (condition : Calls.Condition program (fun name => if name = "x" then some (.int x) else none) P52Ast.requires_has_permuted_multiples_0) :
    (HeapCalls.scalarFunction program "has_permuted_multiples" [.int limit, .int x]).Supported := («Returns» limit x condition).supported
end has_permuted_multiples

namespace naive
open ProjectEulerSolutions.PermutedMultiples

private def body : List Stmt :=
  [.ifThen (.call (.name "has_permuted_multiples") [.name "n", .name "x"]) [.return (.name "x")] [],
    .augAssign (.name "x") .add (.constant (.int 1))]

private theorem loop (limit : Int) (supported : 2 ≤ limit ∧ limit ≤ 6) (first : Nat)
    (positive : 0 < first) (within : first ≤ answer limit) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number limit)) (getX : env "x" = some (number first)) :
    ∃ extra, BlockReturns program env [.whileDo (.constant (.bool true)) body []]
      heap (number (answer limit)) (heap ++ extra) := by
  obtain ⟨allocated, returned⟩ := has_permuted_multiples.result limit first heap
  have tested : Evaluates program env (.call (.name "has_permuted_multiples") [.name "n", .name "x"])
      heap (flag (accepts limit first)) (heap ++ allocated) :=
    Evaluates.call (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getX) .nil)) returned
  by_cases accepted : accepts limit first = true
  · have same : first = answer limit := by have least := answer_minimal limit supported first positive accepted; omega
    refine ⟨allocated, ?_⟩
    apply BlockReturns.while_loop (flag := true) Evaluates.constant rfl
    apply BlockReturns.branch (flag := true) (by simpa only [accepted] using tested) rfl
    exact BlockReturns.return_value (Evaluates.lookup (by simpa only [same] using getX))
  · have earlier : first < answer limit := by
      have winner := answer_accepted limit supported
      by_contra late
      have same : first = answer limit := by omega
      exact accepted (same ▸ winner)
    have rejected : accepts limit first = false := by cases value : accepts limit first <;> simp_all
    let next := setLocal env "x" (number (first+1 : Nat))
    obtain ⟨extra, rest⟩ := loop limit supported (first+1) (by omega) (by omega) (heap ++ allocated) next
      (by simpa [next, setLocal] using getN) (by simp [next, setLocal])
    refine ⟨allocated ++ extra, ?_⟩
    apply BlockReturns.while_loop (flag := true) Evaluates.constant rfl
    apply BlockReturns.branch (flag := false) (by simpa only [rejected] using tested) rfl
    apply BlockReturns.augAssign (value := number (first+1 : Nat)) (middle := heap ++ allocated) (afterOperation := heap ++ allocated)
      getX Evaluates.constant
    · simp [inplace, Mutable.binary, scalarBinary]
    · simpa [body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, List.append_assoc] using rest
termination_by answer limit - first
decreasing_by omega

/-- The positive source enumeration terminates at its genuine least accepted value. -/
theorem result (limit : Int) (supported : 2 ≤ limit ∧ limit ≤ 6) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive" [number limit] heap (number (answer limit)) (heap ++ extra) := by
  let env := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit] []
  obtain ⟨extra, scanned⟩ := loop limit supported 1 (by decide) (answer_positive limit supported) heap
    (setLocal env "x" (number 1)) (by simp [setLocal]; rfl) (by simp [setLocal])
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  exact scanned

theorem «Returns» (limit : Int)
    (lower : Calls.Condition program (fun name => if name = "n" then some (.int limit) else none) P52Ast.requires_naive_0)
    (upper : Calls.Condition program (fun name => if name = "n" then some (.int limit) else none) P52Ast.requires_naive_1) :
    (HeapCalls.scalarFunction program "naive" [.int limit]).Returns := by
  have minimum : 2 ≤ limit := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare lower rfl
  have maximum : limit ≤ 6 := by simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare upper rfl
  obtain ⟨extra, returned⟩ := result limit ⟨minimum, maximum⟩ []
  exact returned.scalar_returns

theorem «Supported» (limit : Int)
    (lower : Calls.Condition program (fun name => if name = "n" then some (.int limit) else none) P52Ast.requires_naive_0)
    (upper : Calls.Condition program (fun name => if name = "n" then some (.int limit) else none) P52Ast.requires_naive_1) :
    (HeapCalls.scalarFunction program "naive" [.int limit]).Supported := («Returns» limit lower upper).supported
end naive

end data.«project-euler-statements».data.py.project_euler_statements.p52
