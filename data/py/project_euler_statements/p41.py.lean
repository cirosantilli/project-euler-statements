import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p41.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerSolutions.Lib.PandigitalPrimeSearch
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerStatements.Lib.PositionalDigits
import lang.py.FormalSW.ScalarSetLemmas

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p41
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.PandigitalPrimeSearch ProjectEulerSolutions.HeapCollection
private abbrev program := P41Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private def numbers (items : List Nat) : List Mutable.Value := items.map number
private def sources (items : List Nat) : List SequenceSource := items.map (fun (n : Nat) => .scalar (.int n))

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 5 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["is_pandigital_n", "naive", "naive_bound"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private def conversionHeap (digits : List Nat) : Mutable.Heap :=
  [.list (numbers digits), .list (numbers digits.reverse)]

private theorem convert_tuple (digits : List Nat) (heap : Mutable.Heap) (address : Nat)
    (env : HeapCalls.Env) (getP : env "p" = some (.ref address))
    (found : heap[address]? = some (.tuple (numbers digits))) :
    Evaluates program env (.call (.name "of_digits_be") [.builtinCall .list [.name "p"]])
      heap (number (value digits)) (heap ++ conversionHeap digits) := by
  have copied : Evaluates program env (.builtinCall .list [.name "p"]) heap
      (.ref heap.length) (heap ++ [.list (numbers digits)]) := by
    apply Evaluates.builtin (.cons (Evaluates.lookup getP) .nil)
    exact primitive_list_tuple heap address (numbers digits) found
  have converted := (common.of_digits_be.result (digits.map (fun (n : Nat) => (n : Int))) 10
    (heap ++ [.list (numbers digits)]) heap.length (by simp [numbers, List.map_map])).extend common_extension
  have defaulted := ReturnsValue.with_defaults (name := "of_digits_be")
    (supplied := [.ref heap.length]) rfl rfl rfl converted
  have interpreted : ProjectEulerStatements.PositionalDigits.value 10
      (digits.map (fun (n : Nat) => (n : Int))).reverse = (value digits : Int) := by
    rw [← List.map_reverse]
    exact ProjectEulerStatements.PositionalDigits.value_naturals 10 digits.reverse
  simpa only [interpreted, conversionHeap, numbers, List.map_map, Function.comp_def,
    List.map_reverse, List.append_assoc, List.singleton_append] using
    Evaluates.call (.cons copied .nil) defaulted

namespace naive
private abbrev conversion : Expr := .call (.name "of_digits_be") [.builtinCall .list [.name "p"]]

private theorem collect_rows (remaining : List (List Nat)) (base : Mutable.Heap)
    (values : List Mutable.Value) (garbage : Mutable.Heap) (env : HeapCalls.Env) :
    ∃ finalEnv finalGarbage, BlockContinues program env
      [.permutationStepLoop "p" (remaining.map sources) [.comprehensionAppend base.length conversion] []]
      (working base values garbage) finalEnv
      (working base (values ++ remaining.map (fun digits => number (value digits))) finalGarbage) := by
  induction remaining generalizing values garbage env with
  | nil =>
      exact ⟨env, garbage, by simpa only [List.map_nil, List.append_nil] using
        (BlockContinues.permutation_done (module := program) (env := env)
          (heap := working base values garbage) BlockContinues.nil)⟩
  | cons head tail ih =>
      let current := working base values garbage
      obtain ⟨address, extra, allocated, tuple⟩ := allocate_tuple (numbers head) current
      let bound := setLocal env "p" (.ref address)
      have evaluated := convert_tuple head (current ++ extra) address bound rfl tuple
      have emitted := emit base values (garbage ++ extra) (conversionHeap head) (number (value head))
        (by simpa only [current, append] using evaluated)
      obtain ⟨finalEnv, finalGarbage, rest⟩ := ih
        (values ++ [number (value head)]) ((garbage ++ extra) ++ conversionHeap head) bound
      refine ⟨finalEnv, finalGarbage, ?_⟩
      simp only [List.map_cons]
      apply BlockContinues.permutation_step (tuple := .ref address) (middle := current ++ extra)
        (by simpa [sources, numbers, List.map_map, Function.comp_def] using allocated)
      simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        Bool.false_or, Bool.false_eq_true, if_false, List.map_cons, List.append_assoc,
        List.singleton_append, current, append] using emitted.append rest
private theorem pool_result (width : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number width)) :
    ∃ extra, Evaluates program env
      (.listComp (.name "i") [("i", .call (.name "range")
        [.constant (.int 1), .binOp (.name "n") .add (.constant (.int 1))], [])])
      heap (.ref heap.length) (working heap (numbers (pool width)) extra) := by
  apply range_map program "i" (.name "i") number
    (values := [number 1, number (width+1)]) (first := 1) (count := width)
  · intro heap env n found
    exact ⟨[], by simpa using Evaluates.lookup (module := program) (heap := heap) found⟩
  · exact .cons Evaluates.constant (.cons
      (Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
        (av := number width) (bv := number 1) (value := number (width+1))
        (Evaluates.lookup getN) Evaluates.constant
        (by simp [Mutable.binary, scalarBinary, number])) .nil)
  · change Except.ok (ε := ExceptionObject) ((1 : Int), ((width+1 : Nat) : Int), (1 : Int)) =
      .ok (1, (1 : Int) + width, 1)
    simp only [Int.natCast_add, Int.natCast_one, Int.add_comm]

private theorem permutations_result (width : Nat) (heap : Mutable.Heap) (address : Nat)
    (env : HeapCalls.Env) (getDigits : env "digits" = some (.ref address))
    (found : heap[address]? = some (.list (numbers (pool width)))) :
    ∃ extra, Evaluates program env
      (.listCompTargets conversion
        [(.name "p", .permutationsIterable [.name "digits", .constant .none], [])])
      heap (.ref heap.length)
      (working heap (numbers ((rows width).map value)) extra) := by
  obtain ⟨finalEnv, extra, executed⟩ := collect_rows (rows width) heap [] []
    (comprehensionTargetsEnv env
      [(.name "p", .permutationsIterable [.name "digits", .constant .none], [])])
  refine ⟨extra, ?_⟩
  apply Evaluates.list_comp_targets_permutations
    (.cons (Evaluates.lookup getDigits) (.cons Evaluates.constant .nil))
  · simpa only [numbers, List.length_map, pool, List.length_range', rows,
      Permutations.rows_map, List.map_map, Function.comp_def, sources, sequenceSource] using
      permutationRows_list heap address (numbers (pool width)) found
  · simpa only [working, List.nil_append, numbers, List.map_map, Function.comp_def,
      comprehensionTargetName, comprehensionTargetBody, comprehensionFilters,
      comprehensionTargetsBody, List.foldr_nil, sources, rows, pool] using executed

private abbrev primeTest : Expr := .call (.name "is_prime") [.name "x"]
private def filterBody (collector : Nat) : List Stmt :=
  [.ifThen primeTest [.comprehensionAppend collector (.name "x")] []]

private theorem filter_loop (items before remaining : List Nat) (split : items = before ++ remaining)
    (base : Mutable.Heap) (address : Nat) (found : base[address]? = some (.list (numbers items)))
    (values : List Mutable.Value) (garbage : Mutable.Heap) (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "x" (.ref address) before.length (filterBody base.length) []]
      (working base values garbage) finalEnv
      (working base (values ++ numbers (remaining.filter (fun n => decide (Nat.Prime n)))) garbage) := by
  induction remaining generalizing before values env with
  | nil =>
      refine ⟨env, ?_⟩
      have current := prefix_found base (.list values :: garbage) address _ found
      apply BlockContinues.sequence_done
        (source := .ref address) (items := numbers items)
        (by simp [sequenceValue, Mutable.sequence, working, current])
        (by simp [split, numbers])
      simpa [numbers] using (BlockContinues.nil (module := program)
        (env := env) (heap := working base values garbage))
  | cons head tail ih =>
      let current := working base values garbage
      let bound := setLocal env "x" (number head)
      have sequence : Mutable.sequence (.ref address) current = some (.ok (numbers items), current) := by
        have entry := prefix_found base (.list values :: garbage) address _ found
        simp [Mutable.sequence, current, working, entry]
      have item : (numbers items)[before.length]? = some (number head) := by
        simp [split, numbers, List.map_append]
      have tested : Evaluates program bound primeTest current
          (.scalar (.bool (decide (Nat.Prime head)))) current :=
        Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
          ((common.HeapPrimeProof.result head current).extend common_extension)
      by_cases prime : Nat.Prime head
      · obtain ⟨finalEnv, rest⟩ := ih (before ++ [head])
          (by simpa [List.append_assoc] using split) (values ++ [number head]) bound
        refine ⟨finalEnv, ?_⟩
        apply BlockContinues.sequence_step (source := .ref address) sequence item
        have emitted := emit (globals := []) base values garbage [] (number head)
          (by simpa only [List.append_nil] using
            (Evaluates.lookup (module := program) (env := bound) (heap := current) (name := "x") (by rfl)))
        have branch : BlockContinues program bound (filterBody base.length) current bound
            (working base (values ++ [number head]) garbage) := by
          apply BlockContinues.branch (flag := true) tested
          · simp [Mutable.truth, prime, scalarTruth]
          · simpa only [List.append_nil] using emitted
        simpa only [filterBody, primeTest, Calls.loopContinuation, Calls.loopControl,
          Calls.loopControlStmt, Bool.false_or, Bool.false_eq_true, if_false,
          List.length_append, List.length_singleton, List.filter_cons, decide_true,
          prime, if_true, numbers, List.map_cons, List.append_assoc,
          List.singleton_append, List.append_nil] using branch.append rest
      · obtain ⟨finalEnv, rest⟩ := ih (before ++ [head])
          (by simpa [List.append_assoc] using split) values bound
        refine ⟨finalEnv, ?_⟩
        apply BlockContinues.sequence_step (source := .ref address) sequence item
        have branch : BlockContinues program bound (filterBody base.length) current bound current := by
          apply BlockContinues.branch (flag := false) tested
          · simp [Mutable.truth, prime, scalarTruth]
          · exact BlockContinues.nil
        simpa only [filterBody, primeTest, Calls.loopContinuation, Calls.loopControl,
          Calls.loopControlStmt, Bool.false_or, Bool.false_eq_true, if_false,
          List.length_append, List.length_singleton, List.filter_cons, decide_false,
          prime, if_neg] using branch.append rest

private theorem filter_result (items : List Nat) (heap : Mutable.Heap) (address : Nat)
    (env : HeapCalls.Env) (getNums : env "nums" = some (.ref address))
    (found : heap[address]? = some (.list (numbers items))) :
    Evaluates program env (.listComp (.name "x") [("x", .name "nums", [primeTest])])
      heap (.ref heap.length)
      (working heap (numbers (items.filter (fun n => decide (Nat.Prime n)))) []) := by
  obtain ⟨finalEnv, executed⟩ := filter_loop items [] items rfl heap address found [] []
    (comprehensionEnv env [("x", .name "nums", [primeTest])])
  apply Evaluates.list_comp_sequence (items := numbers items) (finalEnv := finalEnv) (by intros; simp) (Evaluates.lookup getNums)
    (by simp [Mutable.sequence, found])
  simpa only [filterBody, comprehensionFilters, comprehensionBody, List.length_nil,
    List.nil_append, working] using executed
end naive

private theorem maximum_result (heap : Mutable.Heap) (address : Nat) (items : List Nat)
    (found : heap[address]? = some (.list (numbers items))) (env : HeapCalls.Env)
    (name : String) (getValues : env name = some (.ref address)) :
    Evaluates program env
      (.ifExp (.name name) (.builtinCall .max [.name name]) (.constant (.int 0)))
      heap (number (items.foldl max 0)) heap := by
  cases items with
  | nil =>
      apply Evaluates.conditional (flag := false) (Evaluates.lookup getValues) _ Evaluates.constant
      simp [Mutable.truth, found, numbers]
  | cons first rest =>
      have folded : (rest.map (fun n : Nat => (n : Int))).foldl max (first : Int) =
          ((rest.foldl max first : Nat) : Int) :=
        ProjectEulerStatements.ListMaximum.fold_map (fun n : Nat => (n : Int))
          (by intro a b; dsimp; omega) rest first
      have maximum : Calls.maximumFrom (.int first) (rest.map (fun n : Nat => Constant.int n)) =
          .ok (.int ((rest.foldl max first : Nat) : Int)) := by
        simpa only [List.map_map, Function.comp_def, folded] using
          ScalarSet.maximumFrom_ints (rest.map (fun n : Nat => (n : Int))) first
      apply Evaluates.conditional (flag := true) (Evaluates.lookup getValues)
      · simp [Mutable.truth, found, numbers]
      · apply Evaluates.builtin (.cons (Evaluates.lookup getValues) .nil)
        simp [primitive, Mutable.sequence, found, numbers, number, List.mapM_map,
          Function.comp_def, ScalarSet.maximum, scalarResult, List.mapM_pure, maximum]

namespace naive
/-- The source constructs every permutation and tests every resulting number. -/
theorem result (width : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive" [number width] heap
      (number (best width)) (heap ++ extra) := by
  let initial := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number width] []
  obtain ⟨poolGarbage, pooled⟩ := pool_result width heap initial rfl
  let heap1 := working heap (numbers (pool width)) poolGarbage
  let ready1 := setLocal initial "digits" (.ref heap.length)
  obtain ⟨rowGarbage, permuted⟩ := permutations_result width heap1 heap.length ready1 rfl
    (found heap (numbers (pool width)) poolGarbage)
  let heap2 := working heap1 (numbers ((rows width).map value)) rowGarbage
  let ready2 := setLocal ready1 "nums" (.ref heap1.length)
  have filtered := filter_result ((rows width).map value) heap2 heap1.length ready2 rfl
    (found heap1 (numbers ((rows width).map value)) rowGarbage)
  let heap3 := working heap2 (numbers (candidates width)) []
  let ready3 := setLocal ready2 "vals" (.ref heap2.length)
  have maximum := maximum_result heap3 heap2.length (candidates width)
    (found heap2 (numbers (candidates width)) []) ready3 "vals" rfl
  have executed : ReturnsValue program "naive" [number width] heap
      (number (best width)) heap3 := by
    apply BlockReturns.function rfl rfl
    apply BlockReturns.assign pooled
    apply BlockReturns.assign permuted
    apply BlockReturns.assign filtered
    apply BlockReturns.return_value
    simpa only [best] using maximum
  refine ⟨(.list (numbers (pool width)) :: poolGarbage) ++
    (.list (numbers ((rows width).map value)) :: rowGarbage) ++ [.list (numbers (candidates width))], ?_⟩
  simpa only [heap3, heap2, heap1, working, List.append_assoc, List.singleton_append] using executed

theorem «Returns» (n : Int)
    (condition : Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
      P41Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift n to Nat using nonnegative
  obtain ⟨_, executed⟩ := result n []
  exact executed.scalar_returns

theorem «Supported» (n : Int)
    (condition : Calls.Condition program (fun name => if name = "n" then some (.int n) else none)
      P41Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int n]).Supported :=
  («Returns» n condition).supported
end naive

namespace naive_bound
private theorem values_result (width : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "max_digits" = some (number width)) :
    ∃ extra, Evaluates program env
      (.listComp (.call (.name "naive") [.name "n"]) [("n", .call (.name "range")
        [.constant (.int 1), .binOp (.name "max_digits") .add (.constant (.int 1))], [])])
      heap (.ref heap.length)
      (working heap (numbers ((List.range' 1 width).map best)) extra) := by
  simp only [numbers, List.map_map, Function.comp_def]
  apply range_map program "n" (.call (.name "naive") [.name "n"]) (fun n => number (best n))
    (values := [number 1, number (width+1)]) (first := 1) (count := width)
  · intro heap env n getN
    obtain ⟨extra, executed⟩ := naive.result n heap
    exact ⟨extra, Evaluates.call (.cons (Evaluates.lookup getN) .nil) executed⟩
  · exact .cons Evaluates.constant (.cons
      (Evaluates.binary (middle := heap) (afterRight := heap) (finalHeap := heap)
        (av := number width) (bv := number 1) (value := number (width+1))
        (Evaluates.lookup getN) Evaluates.constant
        (by simp [Mutable.binary, scalarBinary, number])) .nil)
  · change Except.ok (ε := ExceptionObject) ((1 : Int), ((width+1 : Nat) : Int), (1 : Int)) =
      .ok (1, (1 : Int) + width, 1)
    simp only [Int.natCast_add, Int.natCast_one, Int.add_comm]

theorem result (width : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive_bound" [number width] heap
      (number (through width)) (heap ++ extra) := by
  let initial := functionEnv ((findFunctionIn program.body "naive_bound").getD ([], [])).1
    ((findFunctionIn program.body "naive_bound").getD ([], [])).2 [number width] []
  obtain ⟨garbage, collected⟩ := values_result width heap initial rfl
  let collectedHeap := working heap (numbers ((List.range' 1 width).map best)) garbage
  let ready := setLocal initial "values" (.ref heap.length)
  have maximum := maximum_result collectedHeap heap.length ((List.range' 1 width).map best)
    (found heap (numbers ((List.range' 1 width).map best)) garbage) ready "values" rfl
  refine ⟨.list (numbers ((List.range' 1 width).map best)) :: garbage, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign collected
  apply BlockReturns.return_value
  simpa only [List.foldl_map, through] using maximum

theorem «Returns» (max_digits : Int)
    (condition : Calls.Condition program
      (fun name => if name = "max_digits" then some (.int max_digits) else none)
      P41Ast.requires_naive_bound_0) :
    (HeapCalls.scalarFunction program "naive_bound" [.int max_digits]).Returns := by
  have nonnegative : 0 ≤ max_digits := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift max_digits to Nat using nonnegative
  obtain ⟨_, executed⟩ := result max_digits []
  exact executed.scalar_returns

theorem «Supported» (max_digits : Int)
    (condition : Calls.Condition program
      (fun name => if name = "max_digits" then some (.int max_digits) else none)
      P41Ast.requires_naive_bound_0) :
    (HeapCalls.scalarFunction program "naive_bound" [.int max_digits]).Supported :=
  («Returns» max_digits condition).supported
end naive_bound

end data.«project-euler-statements».data.py.project_euler_statements.p41
