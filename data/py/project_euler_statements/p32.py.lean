import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p32.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.TruthCalls
import lang.py.FormalSW.SetSumCalls
import lang.py.FormalSW.ScalarSetLemmas
import ProjectEulerStatements.P32
import Mathlib.Data.List.Dedup
import Mathlib.Data.Int.Basic

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p32
open FormalSW.PyAst HeapCalls
private abbrev program := P32Ast.module
variable {globals : Mutable.Globals}
private abbrev numbers (items : List Int) : List Mutable.Value := items.map (fun n => .scalar (.int n))
private abbrev keys (items : List Int) : List Constant := items.map Constant.int
private theorem set_keys (items : List Int) : (keys items).foldl ScalarSet.insert [] = keys items.eraseDups :=
  ScalarSet.fold_insert_ints items

/-- The predicate on arbitrary integer lists, including out-of-range entries. -/
def pandigital (items : List Int) : Bool :=
  decide (items.length = 9) && items.all (fun n => decide (1 ≤ n ∧ n ≤ 9)) &&
    decide (items.eraseDups.length = 9)

private abbrev allExpression : Expr := .consumeGenerator (.builtinCall .all [])
  (.compare (.constant (.int 1)) [(.ltE, .name "d"), (.ltE, .constant (.int 9))])
  [(.name "d", .name "ds", [])]
private abbrev firstExpression : Expr :=
  .compare (.builtinCall .len [.name "ds"]) [(.eq, .constant (.int 9))]
private abbrev lastExpression : Expr :=
  .compare (.builtinCall .len [.builtinCall .set [.name "ds"]]) [(.eq, .constant (.int 9))]

private theorem in_range (item : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getItem : env "d" = some (.scalar (.int item))) :
    Evaluates (globals := globals) program env (.compare (.constant (.int 1)) [(.ltE, .name "d"), (.ltE, .constant (.int 9))])
      heap (.scalar (.bool (decide (1 ≤ item ∧ item ≤ 9)))) heap := by
  apply Evaluates.chain Evaluates.constant
  by_cases lower : 1 ≤ item
  · apply Evaluates.Compares.next (Evaluates.lookup getItem)
      (compared := .scalar (.bool true)) (afterComparison := heap)
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
    · rfl
    · apply Evaluates.Compares.last (Evaluates.constant (value := .int 9))
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
  · exact Evaluates.Compares.stop (Evaluates.lookup getItem)
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower])
      (by simp [Mutable.truth, scalarTruth, lower])

private theorem all_result (items : List Int) (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getList : env "ds" = some (.ref address)) (found : heap[address]? = some (.list (numbers items))) :
    Evaluates (globals := globals) program env allExpression heap
      (.scalar (.bool (items.all (fun n => decide (1 ≤ n ∧ n ≤ 9))))) heap := by
  apply Evaluates.all_map (values := items) (encode := fun n => .scalar (.int n))
    (by intros; simp) (by intros; simp) (by intros; simp) (Evaluates.lookup getList)
  · simp [Mutable.sequence, found]
  · exact fun env item getItem => in_range (globals := globals) item heap env getItem

private theorem first_result (items : List Int) (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getList : env "ds" = some (.ref address)) (found : heap[address]? = some (.list (numbers items))) :
    Evaluates (globals := globals) program env firstExpression heap (.scalar (.bool (decide (items.length = 9)))) heap := by
  apply Evaluates.compare (av := .scalar (.int items.length)) (bv := .scalar (.int 9))
    (middle := heap) (afterRight := heap)
    (Evaluates.builtin (.cons (Evaluates.lookup getList) .nil)
      (by simp [primitive, Mutable.length, found])) Evaluates.constant
  simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  omega

private theorem last_result (items : List Int) (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getList : env "ds" = some (.ref address)) (found : heap[address]? = some (.list (numbers items))) :
    Evaluates (globals := globals) program env lastExpression heap (.scalar (.bool (decide (items.eraseDups.length = 9))))
      (heap ++ [.set (keys items.eraseDups)]) := by
  have allocated : Evaluates (globals := globals) program env (.builtinCall .set [.name "ds"]) heap (.ref heap.length)
      (heap ++ [.set (keys items.eraseDups)]) := by
    apply Evaluates.builtin (.cons (Evaluates.lookup getList) .nil)
    simpa only [primitive, set_keys] using Mutable.setFrom_list heap address (keys items) (by simpa [numbers, keys, List.map_map] using found)
  apply Evaluates.compare (av := .scalar (.int items.eraseDups.length)) (bv := .scalar (.int 9))
    (middle := heap ++ [.set (keys items.eraseDups)])
    (afterRight := heap ++ [.set (keys items.eraseDups)])
    (Evaluates.builtin (.cons allocated .nil) (by simp [primitive, Mutable.length, keys])) Evaluates.constant
  simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  omega

theorem is_pandigital_1_to_9.result (items : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue (globals := globals) program "is_pandigital_1_to_9" [.ref address] heap
      (.scalar (.bool (pandigital items))) (heap ++ extra) := by
  let env := functionEnv [⟨"ds", some (.subscript (.name "list") (.name "int")), none⟩]
    ((findFunctionIn program.body "is_pandigital_1_to_9").getD ([], [])).2 [.ref address] globals
  have getDs : env "ds" = some (.ref address) := by cases globals <;> rfl
  have first := first_result (globals := globals) items heap address env getDs found
  have all := all_result (globals := globals) items heap address env getDs found
  by_cases length : items.length = 9
  · cases accepted : items.all (fun n => decide (1 ≤ n ∧ n ≤ 9)) with
    | false =>
        refine ⟨[], ?_⟩
        simp only [List.append_nil, pandigital, length, decide_true, Bool.true_and, accepted, Bool.false_and]
        apply BlockReturns.function rfl rfl
        apply BlockReturns.return_value
        apply Evaluates.boolean_next (flag := true) (by simpa [length] using first) rfl rfl
        exact Evaluates.boolean_stop (flag := false) (by simpa only [accepted] using all) rfl rfl
    | true =>
        refine ⟨[.set (keys items.eraseDups)], ?_⟩
        simp only [pandigital, length, decide_true, Bool.true_and, accepted]
        apply BlockReturns.function rfl rfl
        apply BlockReturns.return_value
        apply Evaluates.boolean_next (flag := true) (by simpa [length] using first) rfl rfl
        apply Evaluates.boolean_next (flag := true) (by simpa only [accepted] using all) rfl rfl
        exact Evaluates.boolean_last (last_result (globals := globals) items heap address env getDs found) rfl
  · refine ⟨[], ?_⟩
    simp only [List.append_nil, pandigital, length, decide_false, Bool.false_and]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    exact Evaluates.boolean_stop (flag := false) (by simpa [length] using first) rfl rfl

theorem is_pandigital_1_to_9.«Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "is_pandigital_1_to_9" [.ref address] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  obtain ⟨extra, returned⟩ := is_pandigital_1_to_9.result (globals := []) items heap address found
  exact returned.returns

theorem is_pandigital_1_to_9.«Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "is_pandigital_1_to_9" [.ref address] heap).Supported :=
  (is_pandigital_1_to_9.«Returns» heap address valid typed).supported

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 5 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["is_pandigital_1_to_9", "pandigital_product", "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem found_append {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) (extra : Mutable.Heap) :
    (heap ++ extra)[address]? = some object := by
  have inside : address < heap.length := by
    by_contra outside
    simp [List.getElem?_eq_none (by omega : heap.length ≤ address)] at found
  rw [List.getElem?_append_left inside]
  exact found

private abbrev littleDigits (n : Nat) : List Int := (Nat.digits 10 n).map (fun d : Nat => (d : Int))
private abbrev digits (n : Nat) : List Int := (littleDigits n).reverse
private abbrev allocated (n : Nat) : Mutable.Heap := [.list (numbers (littleDigits n)), .list (numbers (digits n))]

theorem digits_result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue (globals := globals) program "digits_be" [.scalar (.int n)] heap (.ref (heap.length + 1)) (heap ++ allocated n) := by
  apply ReturnsValue.with_defaults rfl rfl rfl
  simpa [allocated, digits, littleDigits, numbers, List.map_map, List.map_reverse, Function.comp_def] using
    (common.digits_be.result (globals := globals) n 10 (by decide) heap).extend common_extension

private theorem digits_found (n : Nat) (heap : Mutable.Heap) :
    (heap ++ allocated n)[heap.length + 1]? = some (.list (numbers (digits n))) := by
  simp [allocated]

private theorem concat_evaluates
    (left : Evaluates (globals := globals) program env lhs heap (.ref a) middle)
    (right : Evaluates (globals := globals) program env rhs middle (.ref b) afterRight)
    (leftFound : afterRight[a]? = some (.list xs))
    (rightFound : afterRight[b]? = some (.list ys)) :
    Evaluates (globals := globals) program env (.binOp lhs .add rhs) heap (.ref afterRight.length)
      (afterRight ++ [.list (xs ++ ys)]) := by
  apply Evaluates.binary left right
  dsimp only [Mutable.binary]
  simp only [show (BinOp.add == BinOp.add) = true from rfl, if_true]
  simp [Mutable.array, leftFound, rightFound, Mutable.allocate, Except.map]

private abbrev tripleDigits (a b : Nat) : List Int := digits a ++ digits b ++ digits (a * b)
private abbrev tripleAllocation (a b : Nat) : Mutable.Heap :=
  allocated a ++ allocated b ++ [.list (numbers (digits a ++ digits b))] ++
    allocated (a * b) ++ [.list (numbers (tripleDigits a b))]
private abbrev productArgument : Expr :=
  .binOp (.binOp (.call (.name "digits_be") [.name "a"]) .add (.call (.name "digits_be") [.name "b"]))
    .add (.call (.name "digits_be") [.binOp (.name "a") .mult (.name "b")])

private theorem triple_digits (a b : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getA : env "a" = some (.scalar (.int a))) (getB : env "b" = some (.scalar (.int b))) :
    Evaluates (globals := globals) program env productArgument heap (.ref (heap.length + 7)) (heap ++ tripleAllocation a b) := by
  let afterA := heap ++ allocated a
  let afterB := afterA ++ allocated b
  let afterAB := afterB ++ [.list (numbers (digits a ++ digits b))]
  let afterP := afterAB ++ allocated (a * b)
  have first := Evaluates.call (.cons (Evaluates.lookup getA) .nil) (digits_result (globals := globals) a heap)
  have second := Evaluates.call (.cons (Evaluates.lookup getB) .nil) (digits_result (globals := globals) b afterA)
  have combined : Evaluates (globals := globals) program env
      (.binOp (.call (.name "digits_be") [.name "a"]) .add (.call (.name "digits_be") [.name "b"]))
      heap (.ref afterB.length) afterAB := by
    simpa [numbers, List.map_append, afterAB, afterB, afterA, List.append_assoc] using concat_evaluates (globals := globals) first second
      (found_append (digits_found a heap) (allocated b)) (digits_found b afterA)
  have product : Evaluates (globals := globals) program env (.binOp (.name "a") .mult (.name "b")) afterAB
      (.scalar (.int ((a * b : Nat) : Int))) afterAB :=
    Evaluates.binary (Evaluates.lookup getA) (Evaluates.lookup getB)
      (by simp [Mutable.binary, scalarBinary])
  have third := Evaluates.call (.cons product .nil) (digits_result (globals := globals) (a * b) afterAB)
  have kept : afterP[afterB.length]? = some (.list (numbers (digits a ++ digits b))) :=
    found_append (by simp [afterAB]) (allocated (a * b))
  have joined := concat_evaluates (globals := globals) combined third kept (digits_found (a * b) afterAB)
  simpa [productArgument, tripleAllocation, afterP, afterAB, afterB, afterA,
    allocated, numbers, tripleDigits, List.map_append, List.append_assoc, Nat.add_assoc] using joined

theorem pandigital_product.raw_result (a b : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue (globals := globals) program "pandigital_product" [.scalar (.int a), .scalar (.int b)] heap
      (.scalar (.bool (pandigital (tripleDigits a b)))) (heap ++ extra) := by
  let initial := heap ++ tripleAllocation a b
  have found : initial[heap.length + 7]? = some (.list (numbers (tripleDigits a b))) := by
    simp [initial, tripleAllocation, allocated, List.append_assoc]
  obtain ⟨extra, returned⟩ := is_pandigital_1_to_9.result (globals := globals) (tripleDigits a b) initial (heap.length + 7) found
  refine ⟨tripleAllocation a b ++ extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  simpa [initial, List.append_assoc] using
    Evaluates.call (.cons (triple_digits (globals := globals) a b heap _ (by cases globals <;> rfl) (by cases globals <;> rfl)) .nil) returned

private theorem eraseDups_cast (items : List Nat) :
    (items.map (fun n : Nat => (n : Int))).eraseDups = items.eraseDups.map (fun n : Nat => (n : Int)) := by
  induction measure : items.length using Nat.strong_induction_on generalizing items with
  | h size ih =>
      cases items with
      | nil => rfl
      | cons head tail =>
          have filtered : (tail.map (fun n : Nat => (n : Int))).filter (fun n => !(n == (head : Int))) =
              (tail.filter (fun n => !(n == head))).map (fun n : Nat => (n : Int)) := by
            rw [List.filter_map]
            congr 1
            apply List.filter_congr
            intro n member
            simp
          simp only [List.map_cons, List.eraseDups_cons]
          rw [filtered]
          rw [ih _ (by have := List.length_filter_le (fun n => !(n == head)) tail; simp only [List.length_cons] at measure; omega)
            (tail.filter (fun n => !(n == head))) rfl]

private theorem folded_all (items : List Nat) (initial : Bool) :
    items.foldl (fun acc d => acc && decide (1 ≤ d ∧ d ≤ 9)) initial =
      (initial && items.all (fun d => decide (1 ≤ d ∧ d ≤ 9))) := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih => simp only [List.foldl_cons, List.all_cons, ih, Bool.and_assoc]

private theorem pandigital_nat (items : List Nat) :
    pandigital (items.map (fun n : Nat => (n : Int))) = ProjectEulerStatements.P32.isPandigital1to9 items := by
  have comparisons : (fun n : Nat => decide (1 ≤ (n : Int) ∧ (n : Int) ≤ 9)) =
      (fun n : Nat => decide (1 ≤ n ∧ n ≤ 9)) := by
    funext n
    have lower : 1 ≤ (n : Int) ↔ 1 ≤ n := by omega
    have upper : (n : Int) ≤ 9 ↔ n ≤ 9 := by omega
    simp only [lower, upper]
  simp only [pandigital, ProjectEulerStatements.P32.isPandigital1to9,
    ProjectEulerStatements.P32.allDigitsOneToNine, folded_all, Bool.true_and,
    eraseDups_cast, List.length_map, List.all_map, Function.comp_def, comparisons]

private theorem product_math (a b : Nat) :
    pandigital (tripleDigits a b) = ProjectEulerStatements.P32.pandigitalProduct a b := by
  simpa [ProjectEulerStatements.P32.pandigitalProduct, ProjectEulerStatements.P32.digitsBE,
    tripleDigits, digits, littleDigits, List.map_reverse, List.map_append] using
    pandigital_nat (ProjectEulerStatements.P32.digitsBE a ++ ProjectEulerStatements.P32.digitsBE b ++
      ProjectEulerStatements.P32.digitsBE (a * b))

theorem pandigital_product.result (a b : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue (globals := globals) program "pandigital_product" [.scalar (.int a), .scalar (.int b)] heap
      (.scalar (.bool (ProjectEulerStatements.P32.pandigitalProduct a b))) (heap ++ extra) := by
  obtain ⟨extra, returned⟩ := pandigital_product.raw_result (globals := globals) a b heap
  exact ⟨extra, by simpa only [product_math] using returned⟩

private abbrev natNumbers (items : List Nat) : List Mutable.Value :=
  numbers (items.map (fun n : Nat => (n : Int)))
private abbrev productTest : Expr := .boolOp .and
  [.name "a", .name "b", .call (.name "pandigital_product") [.name "a", .name "b"]]
private abbrev productExpression : Expr := .binOp (.name "a") .mult (.name "b")
private abbrev emit (collector : Nat) : List Stmt := [.comprehensionAppend collector productExpression]
private abbrev innerBody (collector : Nat) : List Stmt := comprehensionFilters [productTest] (emit collector)
private def selected (a b : Nat) : List Nat :=
  if a = 0 ∨ b = 0 then [] else if ProjectEulerStatements.P32.pandigitalProduct a b then [a * b] else []
private def row (a start count : Nat) : List Nat := (List.range' start count).flatMap (selected a)
private def rows (start count : Nat) (stopB : Int) : List Nat :=
  (List.range' start count).flatMap (fun a => row a 0 stopB.toNat)
private def testValue (a b : Nat) : Mutable.Value :=
  if a = 0 ∨ b = 0 then .scalar (.int 0) else .scalar (.bool (ProjectEulerStatements.P32.pandigitalProduct a b))

private theorem test_result (a b : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getA : env "a" = some (.scalar (.int a))) (getB : env "b" = some (.scalar (.int b))) :
    ∃ extra, Evaluates (globals := globals) program env productTest heap (testValue a b) (heap ++ extra) := by
  by_cases zeroA : a = 0
  · refine ⟨[], ?_⟩
    simp only [List.append_nil, testValue, zeroA, true_or, if_true]
    exact Evaluates.boolean_stop (flag := false) (by simpa [zeroA] using Evaluates.lookup getA) rfl rfl
  · by_cases zeroB : b = 0
    · refine ⟨[], ?_⟩
      simp only [List.append_nil, testValue, zeroB, or_true, if_true]
      apply Evaluates.boolean_next (middle := heap) (flag := true) (Evaluates.lookup getA)
        (by simp [Mutable.truth, scalarTruth, zeroA]) rfl
      exact Evaluates.boolean_stop (flag := false) (by simpa [zeroB] using Evaluates.lookup getB) rfl rfl
    · obtain ⟨extra, returned⟩ := pandigital_product.result (globals := globals) a b heap
      refine ⟨extra, ?_⟩
      simp only [testValue, zeroA, zeroB, false_or, if_false]
      apply Evaluates.boolean_next (middle := heap) (flag := true) (Evaluates.lookup getA)
        (by simp [Mutable.truth, scalarTruth, zeroA]) rfl
      apply Evaluates.boolean_next (middle := heap) (flag := true) (Evaluates.lookup getB)
        (by simp [Mutable.truth, scalarTruth, zeroB]) rfl
      exact Evaluates.boolean_last
        (Evaluates.call (.cons (Evaluates.lookup getA) (.cons (Evaluates.lookup getB) .nil)) returned) rfl

private theorem collector_bound {heap : Mutable.Heap} {collector : Nat} {values : List Mutable.Value}
    (found : heap[collector]? = some (.list values)) : collector < heap.length := by
  by_contra outside
  simp [List.getElem?_eq_none (by omega : heap.length ≤ collector)] at found

private theorem collect_one (a b : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (collector : Nat) (before : List Nat)
    (getA : env "a" = some (.scalar (.int a))) (getB : env "b" = some (.scalar (.int b)))
    (found : heap[collector]? = some (.list (natNumbers before))) :
    ∃ finalHeap, BlockContinues (globals := globals) program env (innerBody collector) heap env finalHeap ∧
      finalHeap[collector]? = some (.list (natNumbers (before ++ selected a b))) := by
  obtain ⟨extra, tested⟩ := test_result (globals := globals) a b heap env getA getB
  have kept := found_append found extra
  by_cases zero : a = 0 ∨ b = 0
  · refine ⟨heap ++ extra, ?_, ?_⟩
    · apply BlockContinues.branch (flag := false) (by simpa [testValue, zero] using tested) rfl
      exact BlockContinues.nil
    · simpa [selected, zero] using kept
  · cases accepted : ProjectEulerStatements.P32.pandigitalProduct a b with
    | false =>
        refine ⟨heap ++ extra, ?_, ?_⟩
        · apply BlockContinues.branch (flag := false) (by simpa [testValue, zero, accepted] using tested) rfl
          exact BlockContinues.nil
        · simpa [selected, zero, accepted] using kept
    | true =>
        let finalHeap := (heap ++ extra).set collector (.list (natNumbers (before ++ [a * b])))
        refine ⟨finalHeap, ?_, ?_⟩
        · apply BlockContinues.branch (flag := true) (by simpa [testValue, zero, accepted] using tested) rfl
          have appended := BlockContinues.comprehension_append (globals := globals) (address := collector)
            (Evaluates.binary (op := .mult) (module := program) (env := env) (heap := heap ++ extra)
              (value := .scalar (.int ((a * b : Nat) : Int))) (finalHeap := heap ++ extra)
              (Evaluates.lookup getA) (Evaluates.lookup getB)
              (by simp [Mutable.binary, scalarBinary])) kept
          simpa [emit, finalHeap, natNumbers, numbers, List.map_append] using appended
        · simpa [selected, zero, accepted, finalHeap] using
            List.getElem?_set_self (l := heap ++ extra) (a := .list (natNumbers (before ++ [a * b]))) (collector_bound kept)

private theorem collect_inner (a count start : Nat) (stop : Int)
    (length : (stop - start).toNat = count) (heap : Mutable.Heap) (collector : Nat)
    (before : List Nat) (env : HeapCalls.Env)
    (getA : env "a" = some (.scalar (.int a)))
    (found : heap[collector]? = some (.list (natNumbers before))) :
    ∃ finalEnv finalHeap,
      BlockContinues (globals := globals) program env [.rangeStepLoop "b" start stop 1 (innerBody collector) []] heap finalEnv finalHeap ∧
      finalHeap[collector]? = some (.list (natNumbers (before ++ row a start count))) ∧
      finalEnv "a" = env "a" ∧ finalEnv "max_b" = env "max_b" := by
  induction count generalizing start heap before env with
  | zero =>
      refine ⟨env, heap, BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil, ?_, rfl, rfl⟩
      simpa [row] using found
  | succ count ih =>
      let boundEnv := setLocal env "b" (.scalar (.int start))
      obtain ⟨middle, one, collected⟩ := collect_one (globals := globals) a start heap boundEnv collector before
        (by simpa [boundEnv, setLocal] using getA) (by simp [boundEnv, setLocal]) found
      obtain ⟨finalEnv, finalHeap, rest, contents, keptA, keptB⟩ := ih (start + 1) (by omega)
        middle (before ++ selected a start) boundEnv
        (by simpa [boundEnv, setLocal] using getA) collected
      refine ⟨finalEnv, finalHeap, ?_, ?_, ?_, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa [innerBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Int.natCast_add, Int.natCast_one] using one.append rest
      · simpa [row, List.range'_succ, List.append_assoc] using contents
      · simpa [boundEnv, setLocal] using keptA
      · simpa [boundEnv, setLocal] using keptB

private abbrev outerBody (collector : Nat) : List Stmt :=
  [.forIn (.name "b") (.call (.name "range") [.binOp (.name "max_b") .add (.constant (.int 1))])
    (innerBody collector) []]

private theorem collect_outer (count start : Nat) (stop maxB : Int)
    (length : (stop - start).toNat = count) (heap : Mutable.Heap) (collector : Nat)
    (before : List Nat) (env : HeapCalls.Env)
    (getB : env "max_b" = some (.scalar (.int maxB)))
    (found : heap[collector]? = some (.list (natNumbers before))) :
    ∃ finalEnv finalHeap,
      BlockContinues (globals := globals) program env [.rangeStepLoop "a" start stop 1 (outerBody collector) []] heap finalEnv finalHeap ∧
      finalHeap[collector]? = some (.list (natNumbers (before ++ rows start count (maxB + 1)))) ∧
      finalEnv "max_b" = env "max_b" := by
  induction count generalizing start heap before env with
  | zero =>
      refine ⟨env, heap, BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil, ?_, rfl⟩
      simpa [rows] using found
  | succ count ih =>
      let boundEnv := setLocal env "a" (.scalar (.int start))
      obtain ⟨middleEnv, middle, inner, contents, _, keptB⟩ := collect_inner (globals := globals) start (maxB + 1).toNat 0
        (maxB + 1) (by simp) heap collector before boundEnv (by simp [boundEnv, setLocal]) found
      have one : BlockContinues (globals := globals) program boundEnv (outerBody collector) heap middleEnv middle := by
        apply BlockContinues.for_range (.cons (Evaluates.binary
          (Evaluates.lookup (by simpa [boundEnv, setLocal] using getB)) Evaluates.constant rfl) .nil) rfl
        exact inner
      obtain ⟨finalEnv, finalHeap, rest, finalContents, finalB⟩ := ih (start + 1) (by omega)
        middle (before ++ row start 0 (maxB + 1).toNat) middleEnv
        (by simpa [boundEnv, setLocal] using keptB.trans (by simpa [boundEnv, setLocal] using getB)) contents
      refine ⟨finalEnv, finalHeap, ?_, ?_, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa [outerBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Int.natCast_add, Int.natCast_one] using one.append rest
      · simpa [rows, List.range'_succ, List.append_assoc] using finalContents
      · simpa [boundEnv, setLocal] using finalB.trans keptB

private abbrev boundsEnv (a b : Int) : ScalarEnv :=
  fun name => if name = "a" then some (.int a) else if name = "b" then some (.int b) else none
private theorem product_domain (a b : Int)
    (condition : Calls.Condition program (boundsEnv a b) P32Ast.requires_pandigital_product_0) : 0 ≤ a ∧ 0 ≤ b := by
  have first : Calls.Evaluates program (boundsEnv a b)
      (.compare (.name "a") [(.gtE, .constant (.int 0))]) (.bool (decide (0 ≤ a))) :=
    Calls.Evaluates.compare (Calls.Evaluates.lookup rfl) Calls.Evaluates.constant (by simp [scalarCompare, evalCmpOp])
  have evaluated : Calls.Evaluates program (boundsEnv a b) P32Ast.requires_pandigital_product_0
      (.bool (decide (0 ≤ a ∧ 0 ≤ b))) := by
    by_cases nonnegative : 0 ≤ a
    · simp only [nonnegative, true_and]
      apply Calls.Evaluates.boolean_continue (by simpa [nonnegative] using first) rfl
      exact Calls.Evaluates.boolean_last
        (Calls.Evaluates.compare (Calls.Evaluates.lookup rfl) Calls.Evaluates.constant
          (by simp [scalarCompare, evalCmpOp]))
    · have rejected : decide (0 ≤ a ∧ 0 ≤ b) = false := by simp [nonnegative]
      rw [rejected]
      exact Calls.Evaluates.boolean_stop (by simpa [nonnegative] using first) rfl
  simpa using evaluated.condition_iff.mp condition

theorem pandigital_product.«Returns» (a b : Int)
    (condition : Calls.Condition program (boundsEnv a b) P32Ast.requires_pandigital_product_0) :
    (HeapCalls.scalarFunction program "pandigital_product" [.int a, .int b]).Returns := by
  have nonnegative := product_domain a b condition
  lift a to Nat using nonnegative.1
  lift b to Nat using nonnegative.2
  obtain ⟨extra, returned⟩ := pandigital_product.result (globals := []) a b []
  exact returned.scalar_returns

theorem pandigital_product.«Supported» (a b : Int)
    (condition : Calls.Condition program (boundsEnv a b) P32Ast.requires_pandigital_product_0) :
    (HeapCalls.scalarFunction program "pandigital_product" [.int a, .int b]).Supported :=
  (pandigital_product.«Returns» a b condition).supported

private abbrev generators : List (String × Expr × List Expr) :=
  [("a", .call (.name "range") [.binOp (.name "max_a") .add (.constant (.int 1))], []),
   ("b", .call (.name "range") [.binOp (.name "max_b") .add (.constant (.int 1))], [productTest])]
private abbrev collectionExpression : Expr := .listComp productExpression generators

def products (maxA maxB : Int) : List Nat := rows 0 (maxA + 1).toNat (maxB + 1)

private theorem collect_result (maxA maxB : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getA : env "max_a" = some (.scalar (.int maxA))) (getB : env "max_b" = some (.scalar (.int maxB))) :
    ∃ finalHeap, Evaluates (globals := globals) program env collectionExpression heap (.ref heap.length) finalHeap ∧
      finalHeap[heap.length]? = some (.list (natNumbers (products maxA maxB))) := by
  obtain ⟨finalEnv, finalHeap, collected, found, _⟩ := collect_outer (globals := globals) (maxA + 1).toNat 0 (maxA + 1) maxB
    (by simp) (heap ++ [.list []]) heap.length [] (comprehensionEnv env generators)
    (by simpa [comprehensionEnv, generators] using getB) (by simp [natNumbers, numbers])
  refine ⟨finalHeap, ?_, by simpa [products] using found⟩
  apply Evaluates.list_comp_range (middle := heap) (finalEnv := finalEnv)
    (values := [.scalar (.int (maxA + 1))])
  · exact .cons (Evaluates.binary (Evaluates.lookup getA) Evaluates.constant rfl) .nil
  · rfl
  · simpa [collectionExpression, generators, comprehensionBody, comprehensionFilters, innerBody, outerBody, emit] using collected

private theorem sum_cast (items : List Nat) :
    (items.map (fun n : Nat => (n : Int))).sum = (items.sum : Int) := by
  induction items with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, List.sum_cons, ih, Int.natCast_add]

/-- Both bounds may be negative; Python's corresponding ranges are empty. -/
theorem naive.raw_result (maxA maxB : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ finalHeap, SetCalls.ReturnsValue (globals := globals) program "naive" [.scalar (.int maxA), .scalar (.int maxB)] heap
      (.scalar (.int (((products maxA maxB).eraseDups.sum : Nat) : Int))) finalHeap := by
  let env := functionEnv [⟨"max_a", some (.name "int"), none⟩, ⟨"max_b", some (.name "int"), none⟩]
    ((findFunctionIn program.body "naive").getD ([], [])).2 [.scalar (.int maxA), .scalar (.int maxB)] globals
  have getA : env "max_a" = some (.scalar (.int maxA)) := by cases globals <;> rfl
  have getB : env "max_b" = some (.scalar (.int maxB)) := by cases globals <;> rfl
  obtain ⟨middle, collected, found⟩ := collect_result (globals := globals) maxA maxB heap env getA getB
  let items := (products maxA maxB).map (fun n : Nat => (n : Int))
  let bound := setLocal env "products" (.ref heap.length)
  let finalHeap := middle ++ [.set (keys items.eraseDups)]
  have allocated : Evaluates (globals := globals) program bound (.builtinCall .set [.name "products"]) middle (.ref middle.length) finalHeap := by
    apply Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil)
    simpa only [primitive, set_keys, finalHeap] using
      Mutable.setFrom_list middle heap.length (keys items)
        (by simpa [items, natNumbers, numbers, keys, List.map_map] using found)
  have summed := SetCalls.Evaluates.sum_integers (module := program) (env := bound)
    (items := items.eraseDups) (initial := 0)
    (.cons allocated (.cons Evaluates.constant .nil)) (by simp [finalHeap, keys])
  refine ⟨finalHeap, ?_⟩
  apply SetCalls.BlockReturns.function rfl rfl
  apply SetCalls.BlockReturns.after_heap (BlockContinues.assign collected)
  apply SetCalls.BlockReturns.return_value
  simpa [items, eraseDups_cast, sum_cast] using summed

private theorem row_fold (a : Nat) (bs acc : List Nat) :
    bs.foldr (fun b rest => if a = 0 ∨ b = 0 then rest
      else if ProjectEulerStatements.P32.pandigitalProduct a b then a * b :: rest else rest) acc =
      bs.flatMap (selected a) ++ acc := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      by_cases zero : a = 0 ∨ b = 0 <;>
        cases accepted : ProjectEulerStatements.P32.pandigitalProduct a b <;>
        simp [selected, zero, accepted, ih]

private theorem products_nat (maxA maxB : Nat) :
    (products maxA maxB).eraseDups.sum = ProjectEulerStatements.P32.naive maxA maxB := by
  have enumerate (as : List Nat) :
      as.foldr (fun a acc => (List.range (maxB + 1)).foldr
        (fun b rest => if a = 0 ∨ b = 0 then rest
          else if ProjectEulerStatements.P32.pandigitalProduct a b then a * b :: rest else rest) acc) [] =
      as.flatMap (fun a => (List.range (maxB + 1)).flatMap (selected a)) := by
    induction as with
    | nil => rfl
    | cons a as ih => rw [List.foldr_cons, row_fold, ih, List.flatMap_cons]
  simp only [ProjectEulerStatements.P32.naive, ProjectEulerStatements.P32.sumPandigitalProducts, enumerate]
  rw [← List.sum_eq_foldl]
  simp [products, rows, row, List.range_eq_range']

theorem naive.result (maxA maxB : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ finalHeap, SetCalls.ReturnsValue (globals := globals) program "naive" [.scalar (.int maxA), .scalar (.int maxB)] heap
      (.scalar (.int (ProjectEulerStatements.P32.naive maxA maxB))) finalHeap := by
  obtain ⟨finalHeap, returned⟩ := naive.raw_result (globals := globals) maxA maxB heap
  exact ⟨finalHeap, by simpa only [products_nat] using returned⟩

theorem naive.«Returns» (maxA maxB : Int) :
    (SetCalls.call program "naive" [.scalar (.int maxA), .scalar (.int maxB)] []).Returns := by
  intro choices
  obtain ⟨finalHeap, returned⟩ := naive.raw_result (globals := []) maxA maxB []
  exact ⟨_, [], finalHeap, 0, returned.finishes choices⟩

theorem naive.«Supported» (maxA maxB : Int) :
    (SetCalls.call program "naive" [.scalar (.int maxA), .scalar (.int maxB)] []).Supported := by
  intro choices
  exact (naive.«Returns» maxA maxB choices).supported

theorem naive_default.result (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ finalHeap, SetCalls.ReturnsValue (globals := globals) program "naive_default" [] heap
      (.scalar (.int (ProjectEulerStatements.P32.naive 99 9999))) finalHeap := by
  obtain ⟨finalHeap, returned⟩ := naive.result (globals := globals) 99 9999 heap
  refine ⟨finalHeap, ?_⟩
  apply SetCalls.BlockReturns.function rfl rfl
  apply SetCalls.BlockReturns.return_value
  exact SetCalls.Evaluates.call (.cons Evaluates.constant (.cons Evaluates.constant .nil)) returned

theorem naive_default.«Returns» : (SetCalls.call program "naive_default" [] []).Returns := by
  intro choices
  obtain ⟨finalHeap, returned⟩ := naive_default.result (globals := []) []
  exact ⟨_, [], finalHeap, 0, returned.finishes choices⟩

theorem naive_default.«Supported» : (SetCalls.call program "naive_default" [] []).Supported := by
  intro choices
  exact (naive_default.«Returns» choices).supported

end data.«project-euler-statements».data.py.project_euler_statements.p32
