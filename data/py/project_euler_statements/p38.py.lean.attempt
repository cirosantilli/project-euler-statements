import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p38.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.TruthCalls
import lang.py.FormalSW.ScalarSetLemmas
import ProjectEulerStatements.Lib.ConcatenatedProductCandidates
import ProjectEulerStatements.Lib.ListMaximum
import Mathlib.Data.List.Range
import Mathlib.Data.List.Dedup

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p38
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.P38
private abbrev program := P38Ast.module
variable {globals : Mutable.Globals}
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (items : List Nat) : List Mutable.Value := items.map number
private abbrev digitHeap (n : Nat) : Mutable.Heap :=
  [.list (numbers (Nat.digits 10 n)), .list (numbers (digitsBE n))]

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 7 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["num_digits", "concat_nat", "concat_product", "is_pandigital_1_to_9",
      "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem digits_result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue (globals := globals) program "digits_be" [number n] heap
      (.ref (heap.length + 1)) (heap ++ digitHeap n) := by
  apply ReturnsValue.with_defaults rfl rfl rfl
  simpa [digitHeap, numbers, number, digitsBE, List.map_reverse, List.map_map] using
    (common.digits_be.result (globals := globals) n 10 (by decide) heap).extend common_extension

theorem num_digits.result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue (globals := globals) program "num_digits" [number n] heap
      (number (numDigits n)) (heap ++ digitHeap n) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin (.cons (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil)
    (digits_result n heap)) .nil)
  simp [primitive, Mutable.length, digitHeap, numbers, digitsBE, numDigits, number]

theorem concat_nat.result (a b : Nat) (heap : Mutable.Heap) :
    ReturnsValue (globals := globals) program "concat_nat" [number a, number b] heap
      (number (concatNat a b)) (heap ++ digitHeap b) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := number (a * 10 ^ numDigits b)) (bv := number b)
    (middle := heap ++ digitHeap b) (afterRight := heap ++ digitHeap b)
  · apply Evaluates.binary (av := number a) (bv := number (10 ^ numDigits b))
      (middle := heap) (afterRight := heap ++ digitHeap b) (Evaluates.lookup (by cases globals <;> rfl))
    · apply Evaluates.binary (av := number 10) (bv := number (numDigits b))
        (middle := heap) (afterRight := heap ++ digitHeap b) Evaluates.constant
        (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) (num_digits.result b heap))
      simp [Mutable.binary, scalarBinary, number, show ¬ (numDigits b : Int) < 0 by omega]
    · simp [Mutable.binary, scalarBinary, number]
  · exact Evaluates.lookup (by cases globals <;> rfl)
  · simp [Mutable.binary, scalarBinary, number, concatNat]

private abbrev productBody : List Stmt :=
  [.assign [.name "acc"] (.call (.name "concat_nat")
    [.name "acc", .binOp (.name "n") .mult (.binOp (.name "i") .add (.constant (.int 1)))])]

private theorem product_loop (n first count total : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getAcc : env "acc" = some (number total)) :
    ∃ extra, BlockReturns (globals := globals) program env
      [.rangeStepLoop "i" first (first + count) 1 productBody [], .return (.name "acc")]
      heap (number ((List.range' first count).foldl (fun acc i => concatNat acc (n * (i + 1))) total))
      (heap ++ extra) := by
  induction count generalizing first total heap env with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [List.range'_zero, List.foldl_nil, List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues])
      exact BlockReturns.return_value (Evaluates.lookup getAcc)
  | succ count ih =>
      let bound := setLocal env "i" (number first)
      let next := concatNat total (n * (first + 1))
      let after := heap ++ digitHeap (n * (first + 1))
      let updated := setLocal bound "acc" (number next)
      obtain ⟨extra, rest⟩ := ih (first + 1) next after updated
        (by simpa [updated, bound, setLocal] using getN) (by simp [updated, setLocal])
      refine ⟨digitHeap (n * (first + 1)) ++ extra, ?_⟩
      simp only [List.range'_succ, List.foldl_cons]
      apply BlockReturns.range_step (by simp [Calls.rangeContinues])
      apply BlockReturns.assign (value := number next) (middle := after)
      · apply Evaluates.call (values := [number total, number (n * (first + 1))])
          (.cons (Evaluates.lookup (by simpa [bound, setLocal] using getAcc)) (.cons
          (Evaluates.binary (av := number n) (bv := number (first + 1))
            (middle := heap) (afterRight := heap) (finalHeap := heap)
            (Evaluates.lookup (by simpa [bound, setLocal] using getN))
            (Evaluates.binary (av := number first) (bv := number 1) (value := number (first + 1))
              (middle := heap) (afterRight := heap) (finalHeap := heap)
              (Evaluates.lookup (by simp [setLocal])) Evaluates.constant
              (by simp [Mutable.binary, scalarBinary, number]))
            (by simp [Mutable.binary, scalarBinary, number])) .nil))
        exact concat_nat.result total (n * (first + 1)) heap
      · simpa [updated, bound, after, next, Nat.add_assoc, Int.add_assoc, Int.add_comm, Int.add_left_comm, productBody, Calls.loopContinuation, Calls.loopControl,
          Calls.loopControlStmt, List.append_assoc] using rest

theorem concat_product.result (n k : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue (globals := globals) program "concat_product" [number n, number k] heap
      (number (concatProduct n k)) (heap ++ extra) := by
  let initial := functionEnv ((findFunctionIn program.body "concat_product").getD ([], [])).1
    ((findFunctionIn program.body "concat_product").getD ([], [])).2 [number n, number k] globals
  obtain ⟨extra, loop⟩ := product_loop (globals := globals) n 0 k 0 heap
    (setLocal initial "acc" (number 0)) (by cases globals <;> rfl) (by simp [setLocal])
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_range (values := [number k]) (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) rfl
  simpa [initial, productBody, List.range_eq_range', concatProduct] using loop

namespace digitPredicate
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

theorem evaluate (items : List Int) (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getDs : env "ds" = some (.ref address))
    (found : heap[address]? = some (.list (numbers items))) :
    ∃ extra, Evaluates (globals := globals) program env
      (.boolOp .and [firstExpression, allExpression, lastExpression]) heap
      (.scalar (.bool (pandigital items))) (heap ++ extra) := by
  have first := first_result (globals := globals) items heap address env getDs found
  have all := all_result (globals := globals) items heap address env getDs found
  by_cases length : items.length = 9
  · cases accepted : items.all (fun n => decide (1 ≤ n ∧ n ≤ 9)) with
    | false =>
        refine ⟨[], ?_⟩
        simp only [List.append_nil, pandigital, length, decide_true, Bool.true_and, accepted, Bool.false_and]
        apply Evaluates.boolean_next (flag := true) (by simpa [length] using first) rfl rfl
        exact Evaluates.boolean_stop (flag := false) (by simpa only [accepted] using all) rfl rfl
    | true =>
        refine ⟨[.set (keys items.eraseDups)], ?_⟩
        simp only [pandigital, length, decide_true, Bool.true_and, accepted]
        apply Evaluates.boolean_next (flag := true) (by simpa [length] using first) rfl rfl
        apply Evaluates.boolean_next (flag := true) (by simpa only [accepted] using all) rfl rfl
        exact Evaluates.boolean_last (last_result (globals := globals) items heap address env getDs found) rfl
  · refine ⟨[], ?_⟩
    simp only [List.append_nil, pandigital, length, decide_false, Bool.false_and]
    exact Evaluates.boolean_stop (flag := false) (by simpa [length] using first) rfl rfl

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

theorem matches_math (n : Nat) :
    pandigital ((digitsBE n).map (fun d : Nat => (d : Int))) = isPandigital1to9 n := by
  have comparisons : (fun d : Nat => decide (1 ≤ (d : Int) ∧ (d : Int) ≤ 9)) =
      (fun d : Nat => decide (1 ≤ d ∧ d ≤ 9)) := by
    funext d
    have lower : 1 ≤ (d : Int) ↔ 1 ≤ d := by omega
    have upper : (d : Int) ≤ 9 ↔ d ≤ 9 := by omega
    simp only [lower, upper]
  simp only [pandigital, isPandigital1to9, allDigitsOneToNine, folded_all, Bool.true_and,
    eraseDups_cast, List.length_map, List.all_map, Function.comp_def, comparisons]

end digitPredicate

theorem is_pandigital_1_to_9.result (n : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue (globals := globals) program "is_pandigital_1_to_9" [number n] heap
      (.scalar (.bool (isPandigital1to9 n))) (heap ++ extra) := by
  let initial := functionEnv ((findFunctionIn program.body "is_pandigital_1_to_9").getD ([], [])).1
    ((findFunctionIn program.body "is_pandigital_1_to_9").getD ([], [])).2 [number n] globals
  let ready := setLocal initial "ds" (.ref (heap.length + 1))
  obtain ⟨extra, tested⟩ := digitPredicate.evaluate (globals := globals)
    ((digitsBE n).map (fun d : Nat => (d : Int))) (heap ++ digitHeap n) (heap.length + 1) ready
    (by simp [ready, setLocal]) (by simp [digitHeap, digitPredicate.numbers, numbers, number, List.map_map])
  refine ⟨digitHeap n ++ extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil)
    (digits_result n heap))
  apply BlockReturns.return_value
  simpa only [digitPredicate.matches_math, List.append_assoc] using tested

namespace naive
open ProjectEulerStatements.ConcatenatedProducts

private abbrev test : Expr := .boolOp .and
  [.compare (.call (.name "num_digits") [.name "v"]) [(.eq, .constant (.int 9))],
   .call (.name "is_pandigital_1_to_9") [.name "v"]]
private abbrev candidateTest (v : Nat) : Bool := decide (numDigits v = 9) && isPandigital1to9 v
private abbrev innerBody : List Stmt :=
  [.ifThen (.compare (.binOp (.name "k") .add (.constant (.int 1))) [(.gt, .constant (.int 1))])
    [.assign [.name "v"] (.call (.name "concat_product")
      [.name "n", .binOp (.name "k") .add (.constant (.int 1))]),
     .ifThen test [.expr (.call (.attribute (.name "vals") "append") [.name "v"])] []] []]
private def selected (n k : Nat) : List Nat :=
  if accepted n (k + 1) then [concatProduct n (k + 1)] else []
private def Stable (before after : HeapCalls.Env) : Prop :=
  after "limit" = before "limit" ∧ after "vals" = before "vals" ∧ after "n" = before "n"

private theorem found_append {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) (extra : Mutable.Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem test_result (v : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getV : env "v" = some (number v)) :
    ∃ extra, Evaluates (globals := globals) program env test heap
      (.scalar (.bool (candidateTest v))) (heap ++ extra) := by
  have first : Evaluates (globals := globals) program env
      (.compare (.call (.name "num_digits") [.name "v"]) [(.eq, .constant (.int 9))])
      heap (.scalar (.bool (decide (numDigits v = 9)))) (heap ++ digitHeap v) := by
    apply Evaluates.compare (av := number (numDigits v)) (bv := number 9)
      (middle := heap ++ digitHeap v) (afterRight := heap ++ digitHeap v)
      (Evaluates.call (.cons (Evaluates.lookup getV) .nil) (num_digits.result v heap)) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    omega
  by_cases nine : numDigits v = 9
  · obtain ⟨extra, second⟩ := is_pandigital_1_to_9.result (globals := globals) v (heap ++ digitHeap v)
    refine ⟨digitHeap v ++ extra, ?_⟩
    simp only [candidateTest, nine, decide_true, Bool.true_and]
    apply Evaluates.boolean_next (flag := true) (by simpa [nine] using first) rfl rfl
    simpa only [List.append_assoc] using Evaluates.boolean_last
      (Evaluates.call (.cons (Evaluates.lookup getV) .nil) second) rfl
  · refine ⟨digitHeap v, ?_⟩
    simp only [candidateTest, nine, decide_false, Bool.false_and]
    exact Evaluates.boolean_stop (flag := false) (by simpa [nine] using first) rfl rfl

private theorem collect_one (n k : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (collector : Nat) (before : List Nat)
    (getN : env "n" = some (number n)) (getK : env "k" = some (number k))
    (getVals : env "vals" = some (.ref collector))
    (found : heap[collector]? = some (.list (numbers before))) :
    ∃ finalEnv finalHeap,
      BlockContinues (globals := globals) program env innerBody heap finalEnv finalHeap ∧
      finalHeap[collector]? = some (.list (numbers (before ++ selected n k))) ∧
      Stable env finalEnv := by
  have guard : Evaluates (globals := globals) program env
      (.compare (.binOp (.name "k") .add (.constant (.int 1))) [(.gt, .constant (.int 1))]) heap
      (.scalar (.bool (decide (1 < k + 1)))) heap := by
    apply Evaluates.compare (av := number (k + 1)) (bv := number 1)
      (middle := heap) (afterRight := heap)
      (Evaluates.binary (av := number k) (bv := number 1) (value := number (k + 1))
        (middle := heap) (afterRight := heap) (finalHeap := heap)
        (Evaluates.lookup getK) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number]))
      Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  by_cases large : 1 < k + 1
  · let v := concatProduct n (k + 1)
    obtain ⟨extra, computed⟩ := concat_product.result (globals := globals) n (k + 1) heap
    let ready := setLocal env "v" (number v)
    have assigned : BlockContinues (globals := globals) program env
        [.assign [.name "v"] (.call (.name "concat_product")
          [.name "n", .binOp (.name "k") .add (.constant (.int 1))])]
        heap ready (heap ++ extra) := by
      apply BlockContinues.assign
      apply Evaluates.call (values := [number n, number (k + 1)])
        (.cons (Evaluates.lookup getN) (.cons
          (Evaluates.binary (av := number k) (bv := number 1) (value := number (k + 1))
            (middle := heap) (afterRight := heap) (finalHeap := heap)
            (Evaluates.lookup getK) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number])) .nil))
      exact computed
    obtain ⟨testExtra, tested⟩ := test_result (globals := globals) v (heap ++ extra) ready (by simp [ready, setLocal])
    have kept := found_append (found_append found extra) testExtra
    have selectedEq : accepted n (k + 1) = candidateTest v := by
      simp only [accepted, large, decide_true, Bool.true_and, candidateTest, v]
    cases yes : candidateTest v with
    | false =>
        refine ⟨ready, (heap ++ extra) ++ testExtra, ?_, ?_, ?_⟩
        · apply BlockContinues.branch (flag := true) (by simpa [large] using guard) rfl
          apply assigned.append
          exact BlockContinues.branch (flag := false) (by simpa only [yes] using tested) rfl .nil
        · simpa [selected, selectedEq, yes] using kept
        · simp [Stable, ready, setLocal]
    | true =>
        let middle := (heap ++ extra) ++ testExtra
        let final := middle.set collector (.list (numbers (before ++ [v])))
        have appended : Evaluates (globals := globals) program ready
            (.call (.attribute (.name "vals") "append") [.name "v"]) middle (.scalar .none) final := by
          have run := Evaluates.append (globals := globals) (module := program) (env := ready)
            (base := .name "vals") (expression := .name "v")
            (old := numbers before) (current := numbers before) (value := number v)
            (Evaluates.lookup (by simpa [ready, setLocal] using getVals)) kept
            (Evaluates.lookup (by simp [ready, setLocal])) kept
          simpa [final, middle, numbers, List.map_append, List.append_assoc] using run
        refine ⟨ready, final, ?_, ?_, ?_⟩
        · apply BlockContinues.branch (flag := true) (by simpa [large] using guard) rfl
          apply assigned.append
          exact BlockContinues.branch (flag := true) (by simpa only [yes] using tested) rfl
            (BlockContinues.discard appended)
        · simpa [selected, selectedEq, yes, final] using
            List.getElem?_set_self (l := middle) (a := .list (numbers (before ++ [v])))
              (List.getElem?_eq_some_iff.mp kept).1
        · simp [Stable, ready, setLocal]
  · refine ⟨env, heap, ?_, ?_, rfl, rfl, rfl⟩
    · exact BlockContinues.branch (flag := false) (by simpa [large] using guard) rfl .nil
    · simpa [selected, accepted, large] using found

private def row (n first count : Nat) : List Nat :=
  (List.range' first count).flatMap (selected n)

private theorem collect_inner (n count first : Nat) (heap : Mutable.Heap) (collector : Nat)
    (before : List Nat) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getVals : env "vals" = some (.ref collector))
    (found : heap[collector]? = some (.list (numbers before))) :
    ∃ finalEnv finalHeap,
      BlockContinues (globals := globals) program env
        [.rangeStepLoop "k" first (first + count) 1 innerBody []] heap finalEnv finalHeap ∧
      finalHeap[collector]? = some (.list (numbers (before ++ row n first count))) ∧
      Stable env finalEnv := by
  induction count generalizing first heap before env with
  | zero =>
      refine ⟨env, heap, ?_, ?_, rfl, rfl, rfl⟩
      · exact BlockContinues.range_done (by simp [Calls.rangeContinues]) .nil
      · simpa [row] using found
  | succ count ih =>
      let bound := setLocal env "k" (number first)
      obtain ⟨middleEnv, middle, one, collected, saved⟩ := collect_one (globals := globals) n first heap bound
        collector before (by simpa [bound, setLocal] using getN) (by simp [bound, setLocal])
        (by simpa [bound, setLocal] using getVals) found
      obtain ⟨finalEnv, finalHeap, rest, contents, stable⟩ := ih (first + 1) middle
        (before ++ selected n first) middleEnv
        (saved.2.2.trans (by simpa [bound, setLocal] using getN))
        (saved.2.1.trans (by simpa [bound, setLocal] using getVals)) collected
      refine ⟨finalEnv, finalHeap, ?_, ?_, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues])
        simpa [innerBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Int.add_assoc, Int.add_comm, Int.add_left_comm] using one.append rest
      · simpa [row, List.range'_succ, List.append_assoc] using contents
      · exact ⟨stable.1.trans (by simpa [bound, setLocal] using saved.1),
          stable.2.1.trans (by simpa [bound, setLocal] using saved.2.1),
          stable.2.2.trans (by simpa [bound, setLocal] using saved.2.2)⟩

private theorem row_seed (n : Nat) : row n 0 9 = seedValues n := by
  have convert (items : List Nat) : items.flatMap (selected n) =
      items.filterMap (fun i => if accepted n (i + 1) then some (concatProduct n (i + 1)) else none) := by
    induction items with
    | nil => rfl
    | cons head tail ih => cases yes : accepted n (head + 1) <;> simp [selected, yes, ih]
  simpa [row, seedValues, List.range_eq_range'] using convert (List.range 9)

private abbrev outerBody : List Stmt :=
  [.forIn (.name "k") (.call (.name "range") [.constant (.int 9)]) innerBody []]
private def rows (first count : Nat) : List Nat :=
  (List.range' first count).flatMap seedValues

private theorem collect_outer (count first : Nat) (heap : Mutable.Heap) (collector : Nat)
    (before : List Nat) (env : HeapCalls.Env)
    (getVals : env "vals" = some (.ref collector))
    (found : heap[collector]? = some (.list (numbers before))) :
    ∃ finalEnv finalHeap,
      BlockContinues (globals := globals) program env
        [.rangeStepLoop "n" first (first + count) 1 outerBody []] heap finalEnv finalHeap ∧
      finalHeap[collector]? = some (.list (numbers (before ++ rows first count))) ∧
      finalEnv "limit" = env "limit" ∧ finalEnv "vals" = env "vals" := by
  induction count generalizing first heap before env with
  | zero =>
      refine ⟨env, heap, ?_, ?_, rfl, rfl⟩
      · exact BlockContinues.range_done (by simp [Calls.rangeContinues]) .nil
      · simpa [rows] using found
  | succ count ih =>
      let bound := setLocal env "n" (number first)
      obtain ⟨middleEnv, middle, inner, collected, stable⟩ := collect_inner (globals := globals) first 9 0
        heap collector before bound (by simp [bound, setLocal])
        (by simpa [bound, setLocal] using getVals) found
      have one : BlockContinues (globals := globals) program bound outerBody heap middleEnv middle := by
        apply BlockContinues.for_range (.cons Evaluates.constant .nil) rfl
        exact inner
      obtain ⟨finalEnv, finalHeap, rest, contents, savedLimit, savedVals⟩ := ih (first + 1) middle
        (before ++ seedValues first) middleEnv
        (stable.2.1.trans (by simpa [bound, setLocal] using getVals))
        (by simpa only [row_seed] using collected)
      refine ⟨finalEnv, finalHeap, ?_, ?_, ?_, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues])
        simpa [outerBody, innerBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Int.add_assoc, Int.add_comm, Int.add_left_comm] using one.append rest
      · simpa [rows, List.range'_succ, List.append_assoc] using contents
      · exact savedLimit.trans (by simpa [bound, setLocal] using stable.1)
      · exact savedVals.trans (by simpa [bound, setLocal] using stable.2.1)

private theorem maximum_result (heap : Mutable.Heap) (address : Nat) (items : List Nat)
    (found : heap[address]? = some (.list (numbers items))) (env : HeapCalls.Env)
    (getVals : env "vals" = some (.ref address)) :
    Evaluates (globals := globals) program env
      (.ifExp (.name "vals") (.builtinCall .max [.name "vals"]) (.constant (.int 0)))
      heap (number (listMax items)) heap := by
  cases items with
  | nil =>
      apply Evaluates.conditional (flag := false) (Evaluates.lookup getVals) _ Evaluates.constant
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
      apply Evaluates.conditional (flag := true) (Evaluates.lookup getVals)
      · simp [Mutable.truth, found, numbers]
      · apply Evaluates.builtin (.cons (Evaluates.lookup getVals) .nil)
        simp [primitive, Mutable.sequence, found, numbers, number, List.mapM_map,
          Function.comp_def, ScalarSet.maximum, scalarResult, List.mapM_pure, maximum, listMax]

theorem result (limit : Nat) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue (globals := globals) program "naive" [number limit] heap
      (number (ProjectEulerStatements.P38.naive limit)) finalHeap := by
  let initial := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit] globals
  let ready := setLocal initial "vals" (.ref heap.length)
  let allocated := heap ++ [.list []]
  obtain ⟨finalEnv, finalHeap, loop, contents, _, savedVals⟩ :=
    collect_outer (globals := globals) (limit + 1) 0 allocated heap.length [] ready
      (by simp [ready, setLocal]) (by simp [allocated, numbers])
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.list .nil)
  apply BlockReturns.for_range (values := [number (limit + 1)]) (middle := allocated)
    (.cons (Evaluates.binary (av := number limit) (bv := number 1) (value := number (limit + 1))
      (middle := allocated) (afterRight := allocated) (finalHeap := allocated)
      (Evaluates.lookup (by cases globals <;> rfl)) Evaluates.constant
      (by simp [Mutable.binary, scalarBinary, number])) .nil) rfl
  apply BlockContinues.returns (body := [.rangeStepLoop "n" 0 (limit + 1) 1 outerBody []])
    (by simpa [ready, initial, outerBody, innerBody] using loop)
  apply BlockReturns.return_value
  have final := maximum_result (globals := globals) finalHeap heap.length (rows 0 (limit + 1))
    (by simpa only [List.nil_append] using contents) finalEnv
    (savedVals.trans (by simp [ready, setLocal]))
  simpa [rows, List.range_eq_range', naive_candidates] using final

theorem «Returns» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P38Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Returns := by
  have nonnegative : 0 ≤ limit := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift limit to Nat using nonnegative
  obtain ⟨_, returned⟩ := result (globals := []) limit []
  exact returned.scalar_returns

theorem «Supported» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P38Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Supported :=
  («Returns» limit condition).supported

end naive

theorem naive_default.result (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue (globals := globals) program "naive_default" [] heap
      (number (ProjectEulerStatements.P38.naive 9999)) finalHeap := by
  obtain ⟨finalHeap, returned⟩ := naive.result (globals := globals) 9999 heap
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.call (.cons Evaluates.constant .nil) returned)

theorem naive_default.«Returns» : (HeapCalls.scalarFunction program "naive_default" []).Returns := by
  obtain ⟨_, returned⟩ := naive_default.result (globals := []) []
  exact ReturnsValue.scalar_returns (values := []) returned

theorem naive_default.«Supported» : (HeapCalls.scalarFunction program "naive_default" []).Supported :=
  naive_default.«Returns».supported

end data.«project-euler-statements».data.py.project_euler_statements.p38
