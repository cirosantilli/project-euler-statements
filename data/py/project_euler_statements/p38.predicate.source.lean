import data.«project-euler-statements».data.py.project_euler_statements.«p38.concat.source»
import ProjectEulerSolutions.Lib.PandigitalDigits
import lang.py.FormalSW.TruthCalls
import lang.py.FormalSW.ScalarSetLemmas

namespace data.«project-euler-statements».data.py.project_euler_statements.p38
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P38
set_option Elab.async false
private abbrev program := P38Ast.module
variable {globals : Mutable.Globals}
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (items : List Nat) : List Mutable.Value := items.map number
private abbrev digitHeap (n : Nat) : Mutable.Heap :=
  [.list (numbers (Nat.digits 10 n)), .list (numbers (digitsBE n))]

namespace digitPredicate
private abbrev numbers (items : List Int) : List Mutable.Value := items.map (fun n => .scalar (.int n))
private abbrev keys (items : List Int) : List Constant := items.map Constant.int
private theorem set_keys (items : List Int) : (keys items).foldl ScalarSet.insert [] = keys items.eraseDups :=
  ScalarSet.fold_insert_ints items

def pandigital (width : Nat) (items : List Int) : Bool :=
  decide (items.length = width) && items.all (fun n => decide (1 ≤ n ∧ n ≤ (width : Int))) &&
    decide (items.eraseDups.length = width)

private abbrev allExpression : Expr := .consumeGenerator (.builtinCall .all [])
  (.compare (.constant (.int 1)) [(.ltE, .name "d"), (.ltE, .name "width")])
  [(.name "d", .name "ds", [])]
private abbrev firstExpression : Expr :=
  .compare (.builtinCall .len [.name "ds"]) [(.eq, .name "width")]
private abbrev lastExpression : Expr :=
  .compare (.builtinCall .len [.builtinCall .set [.name "ds"]]) [(.eq, .name "width")]

private theorem in_range (width : Nat) (item : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getItem : env "d" = some (.scalar (.int item))) (getWidth : env "width" = some (number width)) :
    Evaluates (globals := globals) program env (.compare (.constant (.int 1)) [(.ltE, .name "d"), (.ltE, .name "width")])
      heap (.scalar (.bool (decide (1 ≤ item ∧ item ≤ (width : Int))))) heap := by
  apply Evaluates.chain Evaluates.constant
  by_cases lower : 1 ≤ item
  · apply Evaluates.Compares.next (Evaluates.lookup getItem)
      (compared := .scalar (.bool true)) (afterComparison := heap)
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
    · rfl
    · apply Evaluates.Compares.last (Evaluates.lookup getWidth)
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
  · exact Evaluates.Compares.stop (Evaluates.lookup getItem)
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower])
      (by simp [Mutable.truth, scalarTruth, lower])

private theorem all_result (width : Nat) (items : List Int) (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getList : env "ds" = some (.ref address)) (found : heap[address]? = some (.list (numbers items)))
    (getWidth : env "width" = some (number width)) :
    Evaluates (globals := globals) program env allExpression heap
      (.scalar (.bool (items.all (fun n => decide (1 ≤ n ∧ n ≤ (width : Int)))))) heap := by
  apply Evaluates.all_map_with_invariant (values := items) (encode := fun n => .scalar (.int n))
    (invariant := fun inner => inner "width" = some (number width))
    (by intros; simp) (by intros; simp) (by intros; simp) (Evaluates.lookup getList)
  · simp [Mutable.sequence, found]
  · intro inner item current
    simpa [setLocal] using current
  · simpa [comprehensionTargetsEnv, targetLocals] using getWidth
  · exact fun inner item current getItem => in_range width item heap inner getItem current

private theorem first_result (width : Nat) (items : List Int) (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getList : env "ds" = some (.ref address)) (found : heap[address]? = some (.list (numbers items)))
    (getWidth : env "width" = some (number width)) :
    Evaluates (globals := globals) program env firstExpression heap (.scalar (.bool (decide (items.length = width)))) heap := by
  apply Evaluates.compare (av := number items.length) (bv := number width) (middle := heap) (afterRight := heap)
    (Evaluates.builtin (.cons (Evaluates.lookup getList) .nil)
      (by simp [primitive, Mutable.length, found])) (Evaluates.lookup getWidth)
  simp [HeapCalls.compare, scalarCompare, evalCmpOp]

private theorem last_result (width : Nat) (items : List Int) (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getList : env "ds" = some (.ref address)) (found : heap[address]? = some (.list (numbers items)))
    (getWidth : env "width" = some (number width)) :
    Evaluates (globals := globals) program env lastExpression heap (.scalar (.bool (decide (items.eraseDups.length = width))))
      (heap ++ [.set (keys items.eraseDups)]) := by
  have allocated : Evaluates (globals := globals) program env (.builtinCall .set [.name "ds"]) heap (.ref heap.length)
      (heap ++ [.set (keys items.eraseDups)]) := by
    apply Evaluates.builtin (.cons (Evaluates.lookup getList) .nil)
    simpa only [primitive, set_keys] using Mutable.setFrom_list heap address (keys items)
      (by simpa [numbers, keys, List.map_map] using found)
  apply Evaluates.compare (av := number items.eraseDups.length) (bv := number width)
    (middle := heap ++ [.set (keys items.eraseDups)]) (afterRight := heap ++ [.set (keys items.eraseDups)])
    (Evaluates.builtin (.cons allocated .nil) (by simp [primitive, Mutable.length, keys])) (Evaluates.lookup getWidth)
  simp [HeapCalls.compare, scalarCompare, evalCmpOp]

theorem evaluate (width : Nat) (items : List Int) (heap : Mutable.Heap) (address : Nat) (env : HeapCalls.Env)
    (getDs : env "ds" = some (.ref address)) (found : heap[address]? = some (.list (numbers items)))
    (getWidth : env "width" = some (number width)) :
    ∃ extra, Evaluates (globals := globals) program env (.boolOp .and [firstExpression, allExpression, lastExpression]) heap
      (.scalar (.bool (pandigital width items))) (heap ++ extra) := by
  have first := first_result (globals := globals) width items heap address env getDs found getWidth
  have all := all_result (globals := globals) width items heap address env getDs found getWidth
  by_cases length : items.length = width
  · cases accepted : items.all (fun n => decide (1 ≤ n ∧ n ≤ (width : Int))) with
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
        exact Evaluates.boolean_last (last_result width items heap address env getDs found getWidth) rfl
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

theorem matches_math (width n : Nat) :
    pandigital width ((digitsBE n).map (fun d : Nat => (d : Int))) =
      ProjectEulerSolutions.PandigitalDigits.reference width (digitsBE n) := by
  have comparisons : (fun d : Nat => decide (1 ≤ (d : Int) ∧ (d : Int) ≤ (width : Int))) =
      (fun d : Nat => decide (1 ≤ d ∧ d ≤ width)) := by
    funext d
    have lower : 1 ≤ (d : Int) ↔ 1 ≤ d := by omega
    have upper : (d : Int) ≤ (width : Int) ↔ d ≤ width := by omega
    simp only [lower, upper]
  simp only [pandigital, ProjectEulerSolutions.PandigitalDigits.reference, eraseDups_cast, List.length_map,
    List.all_map, Function.comp_def, comparisons]

end digitPredicate

/-- The independent length, range, and set checks agree with the mathematical digit predicate. -/
theorem is_pandigital.result (n width : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue (globals := globals) program "is_pandigital" [number n, number width] heap
      (.scalar (.bool (ProjectEulerSolutions.PandigitalDigits.check width (digitsBE n)))) (heap ++ extra) := by
  let initial := functionEnv ((findFunctionIn program.body "is_pandigital").getD ([], [])).1
    ((findFunctionIn program.body "is_pandigital").getD ([], [])).2 [number n, number width] globals
  have getInput : initial "n" = some (number n) := by cases globals <;> rfl
  let ready := setLocal initial "ds" (.ref (heap.length + 1))
  obtain ⟨extra, tested⟩ := digitPredicate.evaluate (globals := globals) width ((digitsBE n).map (fun d : Nat => (d : Int)))
    (heap ++ digitHeap n) (heap.length + 1) ready (by simp [ready, setLocal])
    (by simp [digitHeap, digitPredicate.numbers, numbers, number, List.map_map])
    (by cases globals <;> rfl)
  refine ⟨digitHeap n ++ extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup getInput) .nil) (digits_result (globals := globals) n heap))
  apply BlockReturns.return_value
  simpa only [digitPredicate.matches_math, ← ProjectEulerSolutions.PandigitalDigits.check_eq_reference, List.append_assoc] using tested

end data.«project-euler-statements».data.py.project_euler_statements.p38
