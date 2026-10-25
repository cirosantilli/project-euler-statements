import ProjectEulerSolutions.Lib.PokerGroupOrder
import lang.py.FormalSW.MembershipCalls
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerSolutions.Lib.PokerUnique
import lang.py.FormalSW.DictionaryCalls
import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p54.py.ast»
import ProjectEulerSolutions.Lib.PokerTiebreaks
import ProjectEulerSolutions.Lib.PokerStraights
import lang.py.FormalSW.TruthCalls
import lang.py.FormalSW.HeapCalls

/-! Exact source comparison of arbitrary integer keys, including unequal lengths. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p54
open FormalSW.PyAst FormalSW.PyAst.HeapCalls ProjectEulerSolutions.PokerTiebreaks

set_option Elab.async false
private abbrev program := P54Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev numbers (xs : List Int) : List Mutable.Value := xs.map number
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private abbrev args := ((findFunctionIn program.body "lex_gt").getD ([], [])).1
private abbrev body := ((findFunctionIn program.body "lex_gt").getD ([], [])).2
variable {globals : Mutable.Globals}

private abbrev entry (a b : Nat) : HeapCalls.Env := functionEnv args body [.ref a, .ref b] globals
private abbrev first (name : String) : Expr := .subscript (.name name) (.constant (.int 0))
private abbrev tail (name : String) : Expr := .subscript (.name name) (.slice (some (.constant (.int 1))) none none)
private abbrev emptyTest : Expr := .boolOp .or [.unaryOp .not (.name "a"), .unaryOp .not (.name "b")]
private abbrev comparison : Expr := .ifExp (.compare (first "a") [(.eq, first "b")])
  (.call (.name "lex_gt") [tail "a", tail "b"]) (.compare (first "a") [(.gt, first "b")])

private theorem get_a (a b : Nat) : entry (globals := globals) a b "a" = some (.ref a) := by
  cases globals <;> rfl
private theorem get_b (a b : Nat) : entry (globals := globals) a b "b" = some (.ref b) := by
  cases globals <;> rfl

private theorem found_append {heap : Mutable.Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Mutable.Heap) :
    (heap ++ extra)[address]? = some object := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  rw [List.getElem?_append_left inside]
  exact found

private theorem not_list (heap : Mutable.Heap) (env : HeapCalls.Env) (name : String) (address : Nat) (xs : List Int)
    (bound : env name = some (.ref address)) (found : heap[address]? = some (.list (numbers xs))) :
    Evaluates program env (.unaryOp .not (.name name)) heap (flag xs.isEmpty) heap globals := by
  apply Evaluates.unary (Evaluates.lookup bound)
  simp [HeapCalls.unary, Mutable.truth, found, numbers, flag]

private theorem empty_test (left right : List Int) (heap : Mutable.Heap) (a b : Nat)
    (leftFound : heap[a]? = some (.list (numbers left))) (rightFound : heap[b]? = some (.list (numbers right))) :
    Evaluates program (entry (globals := globals) a b) emptyTest heap (flag (left.isEmpty || right.isEmpty)) heap globals := by
  cases left with
  | nil =>
      exact Evaluates.boolean_stop (flag := true)
        (not_list heap (entry (globals := globals) a b) "a" a [] (get_a (globals := globals) a b) leftFound) rfl rfl
  | cons x left =>
      apply Evaluates.boolean_next (flag := false)
        (not_list heap (entry (globals := globals) a b) "a" a (x :: left) (get_a (globals := globals) a b) leftFound) rfl rfl
      exact Evaluates.boolean_last (flag := right.isEmpty)
        (not_list heap (entry (globals := globals) a b) "b" b right (get_b (globals := globals) a b) rightFound) rfl

private theorem head_item (heap : Mutable.Heap) (env : HeapCalls.Env) (name : String) (address : Nat)
    (x : Int) (xs : List Int) (bound : env name = some (.ref address))
    (found : heap[address]? = some (.list (numbers (x :: xs)))) :
    Evaluates program env (first name) heap (number x) heap globals := by
  apply Evaluates.subscript (by intros; simp) (Evaluates.lookup bound) Evaluates.constant
  simpa [numbers, number] using Mutable.getItem_list heap address 0 (numbers (x :: xs)) found (by simp [numbers])

private theorem suffix (heap : Mutable.Heap) (env : HeapCalls.Env) (name : String) (address : Nat)
    (x : Int) (xs : List Int) (bound : env name = some (.ref address))
    (found : heap[address]? = some (.list (numbers (x :: xs)))) :
    Evaluates program env (tail name) heap (.ref heap.length) (heap ++ [.list (numbers xs)]) globals := by
  apply Evaluates.slice (.cons (Evaluates.lookup bound) (.cons Evaluates.constant
    (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
  simpa [numbers] using Mutable.getSlice_list_suffix heap address (numbers (x :: xs)) 1 found

private theorem equal_heads (x y : Int) (left right : List Int) (heap : Mutable.Heap) (a b : Nat)
    (leftFound : heap[a]? = some (.list (numbers (x :: left))))
    (rightFound : heap[b]? = some (.list (numbers (y :: right)))) :
    Evaluates program (entry (globals := globals) a b) (.compare (first "a") [(.eq, first "b")]) heap
      (flag (decide (x = y))) heap globals := by
  apply Evaluates.compare (av := number x) (bv := number y) (middle := heap) (afterRight := heap)
    (head_item heap (entry (globals := globals) a b) "a" a x left (get_a (globals := globals) a b) leftFound)
    (head_item heap (entry (globals := globals) a b) "b" b y right (get_b (globals := globals) a b) rightFound)
  simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]

private theorem greater_heads (x y : Int) (left right : List Int) (heap : Mutable.Heap) (a b : Nat)
    (leftFound : heap[a]? = some (.list (numbers (x :: left))))
    (rightFound : heap[b]? = some (.list (numbers (y :: right)))) :
    Evaluates program (entry (globals := globals) a b) (.compare (first "a") [(.gt, first "b")]) heap
      (flag (decide (y < x))) heap globals := by
  apply Evaluates.compare (av := number x) (bv := number y) (middle := heap) (afterRight := heap)
    (head_item heap (entry (globals := globals) a b) "a" a x left (get_a (globals := globals) a b) leftFound)
    (head_item heap (entry (globals := globals) a b) "b" b y right (get_b (globals := globals) a b) rightFound)
  simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]

private theorem empty_return (left right : List Int) (heap : Mutable.Heap) (a b : Nat)
    (leftFound : heap[a]? = some (.list (numbers left))) (rightFound : heap[b]? = some (.list (numbers right)))
    (empty : (left.isEmpty || right.isEmpty) = true) :
    ReturnsValue program "lex_gt" [.ref a, .ref b] heap (flag false) heap globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := true) (value := flag true) (middle := heap)
  · simpa only [empty] using empty_test (globals := globals) left right heap a b leftFound rightFound
  · rfl
  · exact BlockReturns.return_value Evaluates.constant

private theorem nonempty_return (x y : Int) (left right : List Int) (heap : Mutable.Heap) (a b : Nat)
    (leftFound : heap[a]? = some (.list (numbers (x :: left))))
    (rightFound : heap[b]? = some (.list (numbers (y :: right))))
    (value : Mutable.Value) (finalHeap : Mutable.Heap)
    (evaluated : Evaluates program (entry (globals := globals) a b) comparison heap value finalHeap globals) :
    ReturnsValue program "lex_gt" [.ref a, .ref b] heap value finalHeap globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := false) (value := flag false) (middle := heap)
  · exact empty_test (x :: left) (y :: right) heap a b leftFound rightFound
  · rfl
  · exact BlockReturns.return_value evaluated

/-- The source keeps every caller object and allocates only the recursive tail slices. -/
theorem lex_gt.result (left right : List Int) (heap : Mutable.Heap) (a b : Nat)
    (leftFound : heap[a]? = some (.list (numbers left))) (rightFound : heap[b]? = some (.list (numbers right))) :
    ∃ extra, ReturnsValue program "lex_gt" [.ref a, .ref b] heap
      (flag (referenceGreater left right)) (heap ++ extra) globals := by
  induction left generalizing right heap a b with
  | nil =>
      refine ⟨[], ?_⟩
      simpa only [referenceGreater, List.append_nil] using empty_return [] right heap a b leftFound rightFound rfl
  | cons x left ih =>
      cases right with
      | nil =>
          refine ⟨[], ?_⟩
          simpa only [referenceGreater, List.append_nil] using
            empty_return (x :: left) [] heap a b leftFound rightFound rfl
      | cons y right =>
          by_cases same : x = y
          · subst y
            let firstHeap := heap ++ [Mutable.Object.list (numbers left)]
            let bothHeap := firstHeap ++ [Mutable.Object.list (numbers right)]
            have secondPreserved : firstHeap[b]? = some (.list (numbers (x :: right))) := found_append rightFound _
            have firstSlice : bothHeap[heap.length]? = some (.list (numbers left)) := by
              simp [bothHeap, firstHeap, List.append_assoc]
            have secondSlice : bothHeap[firstHeap.length]? = some (.list (numbers right)) := by simp [bothHeap]
            obtain ⟨extra, recursive⟩ := ih right bothHeap heap.length firstHeap.length firstSlice secondSlice
            have finished : ReturnsValue program "lex_gt" [.ref a, .ref b] heap
                (flag (referenceGreater left right)) (bothHeap ++ extra) globals := by
              apply nonempty_return x x left right heap a b leftFound rightFound
              apply Evaluates.conditional (flag := true) (value := flag true) (middle := heap)
              · simpa using equal_heads (globals := globals) x x left right heap a b leftFound rightFound
              · rfl
              · exact Evaluates.call (.cons (suffix heap (entry (globals := globals) a b) "a" a x left (get_a (globals := globals) a b) leftFound)
                  (.cons (suffix firstHeap (entry (globals := globals) a b) "b" b x right (get_b (globals := globals) a b) secondPreserved) .nil)) recursive
            refine ⟨[.list (numbers left), .list (numbers right)] ++ extra, ?_⟩
            simpa only [referenceGreater, if_pos rfl, bothHeap, firstHeap, List.append_assoc,
              List.cons_append, List.nil_append] using finished
          · refine ⟨[], ?_⟩
            simp only [List.append_nil, referenceGreater, if_neg same]
            apply nonempty_return x y left right heap a b leftFound rightFound
            apply Evaluates.conditional (flag := false) (value := flag false) (middle := heap)
            · simpa [same] using equal_heads (globals := globals) x y left right heap a b leftFound rightFound
            · rfl
            · exact greater_heads x y left right heap a b leftFound rightFound

theorem lex_gt.«Returns» (heap : Mutable.Heap) (a b : Nat) (_valid : heap.Valid)
    (left : Mutable.Value.HasType heap (.ref a) "list[int]")
    (right : Mutable.Value.HasType heap (.ref b) "list[int]") :
    (HeapCalls.call program "lex_gt" [.ref a, .ref b] heap).Returns := by
  obtain ⟨xs, leftFound⟩ := Mutable.Value.ints_of_hasType left
  obtain ⟨ys, rightFound⟩ := Mutable.Value.ints_of_hasType right
  obtain ⟨extra, result⟩ := lex_gt.result (globals := []) xs ys heap a b leftFound rightFound
  exact result.returns

theorem lex_gt.«ReturnType» (heap : Mutable.Heap) (a b : Nat) (_valid : heap.Valid)
    (left : Mutable.Value.HasType heap (.ref a) "list[int]")
    (right : Mutable.Value.HasType heap (.ref b) "list[int]") :
    (HeapCalls.call program "lex_gt" [.ref a, .ref b] heap).ReturnType "bool" := by
  obtain ⟨xs, leftFound⟩ := Mutable.Value.ints_of_hasType left
  obtain ⟨ys, rightFound⟩ := Mutable.Value.ints_of_hasType right
  obtain ⟨extra, result⟩ := lex_gt.result (globals := []) xs ys heap a b leftFound rightFound
  exact .inr ⟨flag (referenceGreater xs ys), [], heap ++ extra, heap.length, result.finishes, rfl⟩

theorem lex_gt.«Supported» (heap : Mutable.Heap) (a b : Nat) (valid : heap.Valid)
    (left : Mutable.Value.HasType heap (.ref a) "list[int]")
    (right : Mutable.Value.HasType heap (.ref b) "list[int]") :
    (HeapCalls.call program "lex_gt" [.ref a, .ref b] heap).Supported :=
  (lex_gt.«Returns» heap a b valid left right).supported

namespace sorted_ranks

private abbrev params := ((findFunctionIn program.body "sorted_ranks").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "sorted_ranks").getD ([], [])).2
private abbrev initial (context : Mutable.Globals) (address : Nat) : HeapCalls.Env :=
  functionEnv params sourceBody [.ref address] context

private theorem get_rs (context : Mutable.Globals) (address : Nat) :
    initial context address "rs" = some (.ref address) := by
  cases context <;> rfl

/-- Sorting returns a fresh list and keeps the caller's original list and aliases intact. -/
theorem result (input : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers input))) :
    ReturnsValue program "sorted_ranks" [.ref address] heap (.ref heap.length)
      (heap ++ [.list (numbers (ScalarSort.ints input))]) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin (.cons (Evaluates.lookup (get_rs globals address)) .nil)
  simpa [List.map_map, numbers, number, Function.comp_def] using
    primitive_sorted_list heap address (input.map Constant.int) ((ScalarSort.ints input).map Constant.int)
      (by simpa [List.map_map, numbers, number, Function.comp_def] using found) (ScalarSort.sort_ints input)

theorem «Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "sorted_ranks" [.ref address] heap).Returns := by
  obtain ⟨input, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (result (globals := []) input heap address found).returns

theorem «ReturnType» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "sorted_ranks" [.ref address] heap).ReturnType "list[int]" := by
  obtain ⟨input, found⟩ := Mutable.Value.ints_of_hasType typed
  refine .inr ⟨.ref heap.length, [], _, heap.length, (result (globals := []) input heap address found).finishes, ?_⟩
  simp [Mutable.Value.HasType, numbers, number]
  exact ⟨"int", rfl, by simp⟩

theorem «Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "sorted_ranks" [.ref address] heap).Supported :=
  («Returns» heap address valid typed).supported

end sorted_ranks

namespace straight_high

def wheel : List Int := [2, 3, 4, 5, 14]

/-- The source's wheel exception and last-or-zero result, for arbitrary integer lists. -/
def value (input : List Int) : Int :=
  if ScalarSort.ints input = wheel then 5 else (ScalarSort.ints input).getLastD 0

private abbrev params := ((findFunctionIn program.body "straight_high").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "straight_high").getD ([], [])).2
private abbrev initial (context : Mutable.Globals) (address : Nat) : HeapCalls.Env :=
  functionEnv params sourceBody [.ref address] context
private abbrev wheelExpression : Expr := .list
  [.constant (.int 2), .constant (.int 3), .constant (.int 4), .constant (.int 5), .constant (.int 14)]
private abbrev lastExpression : Expr := .subscript (.name "rs") (.unaryOp .uSub (.constant (.int 1)))
private abbrev lastOrZero : Expr := .ifExp (.name "rs") lastExpression (.constant (.int 0))

private theorem get_rs (context : Mutable.Globals) (address : Nat) :
    initial context address "rs" = some (.ref address) := by
  cases context <;> rfl

private theorem wheel_test (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat) (items : List Int)
    (bound : env "rs" = some (.ref address)) (found : heap[address]? = some (.list (numbers items))) :
    Evaluates program env (.compare (.name "rs") [(.eq, wheelExpression)]) heap
      (flag (decide (items = wheel))) (heap ++ [.list (numbers wheel)]) globals := by
  let afterWheel := heap ++ [Mutable.Object.list (numbers wheel)]
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have different : address ≠ heap.length := by omega
  have original : afterWheel[address]? = some (.list (numbers items)) := found_append found _
  have literal : afterWheel[heap.length]? = some (.list (numbers wheel)) := by simp [afterWheel]
  apply Evaluates.compare (av := .ref address) (bv := .ref heap.length) (middle := heap) (afterRight := afterWheel)
  · exact Evaluates.lookup bound
  · exact Evaluates.list (.cons Evaluates.constant (.cons Evaluates.constant
      (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil)))))
  · simp [HeapCalls.compare, Mutable.array, original, literal, different, equalLists_ints, numbers, flag]
    exact ⟨rfl, rfl⟩

private theorem last_item_result (values : List Int) (last : Int) (lastValue : values.getLast? = some last)
    (heap : Mutable.Heap) (address : Nat) (found : heap[address]? = some (.list (numbers values))) :
    Mutable.getItem (.ref address) (number (-1)) heap = some (.ok (number last), heap) := by
  obtain ⟨before, rfl⟩ := List.getLast?_eq_some_iff.mp lastValue
  have cancel : (-1 : Int) + ((before.length : Int) + 1) = (before.length : Int) := by omega
  have low : ¬ (before.length : Int) < 0 := by omega
  have high : ¬ (before.length : Int) + 1 ≤ (before.length : Int) := by omega
  simp [Mutable.getItem, found, Mutable.index, numbers, number, cancel, low, high, Except.map]

private theorem last_item (heap : Mutable.Heap) (address : Nat) (x : Int) (items : List Int)
    (found : heap[address]? = some (.list (numbers (x :: items)))) :
    Mutable.getItem (.ref address) (number (-1)) heap =
      some (.ok (number ((x :: items).getLastD 0)), heap) := by
  have originalLast : (x :: items).getLast? = some ((x :: items).getLastD 0) := by
    simp only [List.getLastD_eq_getLast?, List.getLast?_cons, Option.getD_some]
  exact last_item_result (x :: items) ((x :: items).getLastD 0) originalLast heap address found

private theorem last_or_zero (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat) (items : List Int)
    (bound : env "rs" = some (.ref address)) (found : heap[address]? = some (.list (numbers items))) :
    Evaluates program env lastOrZero heap (number (items.getLastD 0)) heap globals := by
  cases items with
  | nil =>
      apply Evaluates.conditional (flag := false) (value := .ref address) (middle := heap)
        (Evaluates.lookup bound)
      · simp [Mutable.truth, found, numbers]
      · exact Evaluates.constant
  | cons x items =>
      apply Evaluates.conditional (flag := true) (value := .ref address) (middle := heap)
        (Evaluates.lookup bound)
      · simp [Mutable.truth, found, numbers]
      · apply Evaluates.subscript (by intros; simp) (Evaluates.lookup bound)
          (Evaluates.unary Evaluates.constant rfl)
        exact last_item heap address x items found

/-- Both the sorted copy and the wheel literal are fresh, preserving every caller object. -/
theorem result (input : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers input))) :
    ReturnsValue program "straight_high" [.ref address] heap (number (value input))
      (heap ++ [.list (numbers (ScalarSort.ints input)), .list (numbers wheel)]) globals := by
  let firstHeap := heap ++ [Mutable.Object.list (numbers (ScalarSort.ints input))]
  let finalHeap := firstHeap ++ [Mutable.Object.list (numbers wheel)]
  let ready := setLocal (initial globals address) "rs" (.ref heap.length)
  have sortedFound : firstHeap[heap.length]? = some (.list (numbers (ScalarSort.ints input))) := by simp [firstHeap]
  have retained : finalHeap[heap.length]? = some (.list (numbers (ScalarSort.ints input))) := found_append sortedFound _
  have finished : ReturnsValue program "straight_high" [.ref address] heap (number (value input)) finalHeap globals := by
    apply BlockReturns.function rfl rfl
    apply BlockReturns.assign
      (Evaluates.call (.cons (Evaluates.lookup (get_rs globals address)) .nil)
        (sorted_ranks.result (globals := globals) input heap address found))
    apply BlockReturns.return_value
    apply Evaluates.conditional (flag := decide (ScalarSort.ints input = wheel))
      (value := flag (decide (ScalarSort.ints input = wheel))) (middle := finalHeap)
    · exact wheel_test firstHeap ready heap.length (ScalarSort.ints input) rfl sortedFound
    · rfl
    · by_cases same : ScalarSort.ints input = wheel
      · simpa [value, same] using (Evaluates.constant :
          Evaluates program ready (.constant (.int 5)) finalHeap (number 5) finalHeap globals)
      · simpa [value, same] using last_or_zero (globals := globals) finalHeap ready heap.length (ScalarSort.ints input) rfl retained
  simpa [firstHeap, finalHeap, List.append_assoc] using finished

theorem «Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "straight_high" [.ref address] heap).Returns := by
  obtain ⟨input, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (result (globals := []) input heap address found).returns

theorem «ReturnType» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "straight_high" [.ref address] heap).ReturnType "int" := by
  obtain ⟨input, found⟩ := Mutable.Value.ints_of_hasType typed
  exact .inr ⟨number (value input), [], _, heap.length, (result (globals := []) input heap address found).finishes, rfl⟩

theorem «Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "straight_high" [.ref address] heap).Supported :=
  («Returns» heap address valid typed).supported

end straight_high

end data.«project-euler-statements».data.py.project_euler_statements.p54

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.is_straight
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
set_option Elab.async false

private abbrev program := P54Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev numbers (values : List Int) : List Mutable.Value := values.map number
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev params := ((findFunctionIn program.body "is_straight").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "is_straight").getD ([], [])).2
private abbrev initial (globals : Mutable.Globals) (address : Nat) : HeapCalls.Env :=
  functionEnv params sourceBody [.ref address] globals
private abbrev wheel := ProjectEulerSolutions.PokerStraights.wheel
private abbrev wheelExpression : Expr := .list
  [.constant (.int 2), .constant (.int 3), .constant (.int 4), .constant (.int 5), .constant (.int 14)]
private abbrev predicate : Expr := .compare (.name "r")
  [(.eq, .binOp (.subscript (.name "rs") (.constant (.int 0))) .add (.name "i"))]
private abbrev generators : List (Expr × Expr × List Expr) :=
  [(.tuple [.name "i", .name "r"], .call (.name "enumerate") [.name "rs", .constant (.int 0)], [])]
private abbrev allExpression : Expr := .consumeGenerator (.builtinCall .all []) predicate generators
private abbrev boolExpression : Expr := .unaryOp .not (.unaryOp .not (.name "rs"))

private theorem found_append {heap : Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem get_rs (globals : Mutable.Globals) (address : Nat) :
    initial globals address "rs" = some (.ref address) := by
  cases globals <;> rfl

private theorem wheel_test (heap : Heap) (env : HeapCalls.Env) (address : Nat) (items : List Int)
    (globals : Mutable.Globals) (bound : env "rs" = some (.ref address))
    (found : heap[address]? = some (.list (numbers items))) :
    Evaluates program env (.compare (.name "rs") [(.eq, wheelExpression)]) heap
      (flag (decide (items = wheel))) (heap ++ [.list (numbers wheel)]) globals := by
  let afterWheel := heap ++ [Mutable.Object.list (numbers wheel)]
  have inside := (List.getElem?_eq_some_iff.mp found).1
  have different : address ≠ heap.length := by omega
  have original : afterWheel[address]? = some (.list (numbers items)) := found_append found _
  have literal : afterWheel[heap.length]? = some (.list (numbers wheel)) := by simp [afterWheel]
  apply Evaluates.compare (av := .ref address) (bv := .ref heap.length) (middle := heap) (afterRight := afterWheel)
  · exact Evaluates.lookup bound
  · exact Evaluates.list (.cons Evaluates.constant (.cons Evaluates.constant
      (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil)))))
  · simp [HeapCalls.compare, Mutable.array, original, literal, different, equalLists_ints, numbers, flag]
    exact ⟨rfl, rfl⟩

private theorem tested (heap : Heap) (env : HeapCalls.Env) (address : Nat) (first value : Int)
    (tail : List Int) (index : Nat) (globals : Mutable.Globals)
    (bound : env "rs" = some (.ref address)) (found : heap[address]? = some (.list (numbers (first :: tail))))
    (getIndex : env "i" = some (number (index : Int))) (getRank : env "r" = some (number value)) :
    Evaluates program env predicate heap (flag (decide (value = first + (index : Int)))) heap globals := by
  apply Evaluates.compare (av := number value) (bv := number (first + (index : Int)))
    (middle := heap) (afterRight := heap) (Evaluates.lookup getRank)
  · apply Evaluates.binary (av := number first) (bv := number (index : Int)) (middle := heap) (afterRight := heap)
    · apply Evaluates.subscript (by intros; simp) (Evaluates.lookup bound) Evaluates.constant
      simp [Mutable.getItem, found, Mutable.index, numbers, number, Except.map]
    · exact Evaluates.lookup getIndex
    · rfl
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]

/-- The source consumer binds the two immediately unpacked enumerate fields directly. -/
private theorem enumerate_step (heap : Heap) (env : HeapCalls.Env) (address position : Nat)
    (items : List Mutable.Value) (value : Mutable.Value) (counter : Int) (body following : List Stmt)
    (answer : Mutable.Value) (finalHeap : Heap) (globals : Mutable.Globals)
    (sequence : Mutable.sequence (.ref address) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockReturns program (setLocal (setLocal env "i" (number counter)) "r" value)
      (body ++ [Calls.loopContinuation body (.enumerateStepLoop "i" "r" (.ref address)
        (position+1) (counter+1) body [])] ++ following) heap answer finalHeap globals) :
    BlockReturns program env (.enumerateStepLoop "i" "r" (.ref address) position counter body [] :: following)
      heap answer finalHeap globals := by
  intro anchors stack
  exact .next (by simp [step, run, sequenceValue, sequence, item]) (rest anchors stack)

private theorem all_loop (heap : Heap) (address : Nat) (first : Int) (tail remaining : List Int)
    (found : heap[address]? = some (.list (numbers (first :: tail)))) (position : Nat)
    (suffix : (first :: tail).drop position = remaining) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (bound : env "rs" = some (.ref address)) :
    BlockReturns program env
      [.enumerateStepLoop "i" "r" (.ref address) position (position : Int) (truthBody true predicate) [],
        .return (.constant (.bool true))] heap
      (flag ((remaining.zipIdx position).all (fun pair => decide (pair.1 = first + (pair.2 : Int))))) heap globals := by
  have sequence : Mutable.sequence (.ref address) heap = some (.ok (numbers (first :: tail)), heap) := by
    simp [Mutable.sequence, found]
  induction remaining generalizing position env with
  | nil =>
      have missing : (first :: tail)[position]? = none := by
        simpa [suffix] using (List.head?_drop (l := first :: tail) (i := position)).symm
      intro anchors stack
      refine .next ?_ ((BlockReturns.return_value (module := program) (env := env)
        (globals := globals) (rest := []) Evaluates.constant) anchors stack)
      have absent : (numbers (first :: tail))[position]? = none := by
        simp only [numbers, List.getElem?_map, missing, Option.map_none]
      simp only [numbers, List.map_cons] at absent
      simp [step, run, sequenceValue, sequence, absent]
  | cons value rest ih =>
      have item : (first :: tail)[position]? = some value := by
        simpa [suffix] using (List.head?_drop (l := first :: tail) (i := position)).symm
      let ready := setLocal (setLocal env "i" (number (position : Int))) "r" (number value)
      have retained : ready "rs" = some (.ref address) := by simpa [ready, setLocal] using bound
      have evaluated := tested heap ready address first value tail position globals retained found
        (by simp [ready, setLocal]) (by simp [ready, setLocal])
      apply enumerate_step heap env address position (numbers (first :: tail)) (number value) (position : Int)
        (truthBody true predicate) [.return (.constant (.bool true))] _ heap globals sequence
        (by simp only [numbers, List.getElem?_map, item, Option.map_some])
      rw [List.zipIdx_cons, List.all_cons]
      cases accepted : decide (value = first + (position : Int)) with
      | false =>
          simp only [Bool.false_and]
          apply BlockReturns.branch (flag := false) (by simpa only [accepted] using evaluated) rfl
          exact BlockReturns.return_value Evaluates.constant
      | true =>
          simp only [Bool.true_and]
          apply BlockReturns.branch (flag := true) (by simpa only [accepted] using evaluated) rfl
          have continued := ih (position+1)
            (by simp [List.drop_add_one_eq_tail_drop, suffix]) ready retained
          simpa [truthBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            Int.natCast_add, Int.natCast_one] using continued

private theorem all_enumerate (heap : Heap) (env : HeapCalls.Env) (address : Nat) (first : Int)
    (tail : List Int) (globals : Mutable.Globals) (bound : env "rs" = some (.ref address))
    (found : heap[address]? = some (.list (numbers (first :: tail)))) :
    Evaluates program env allExpression heap
      (flag (ProjectEulerSolutions.PokerStraights.consecutive (first :: tail))) heap globals := by
  let inside := comprehensionTargetsEnv env generators
  have captured : inside "rs" = some (.ref address) := by
    simpa [inside, comprehensionTargetsEnv, targetLocals] using bound
  have executed := all_loop heap address first tail (first :: tail) found 0 rfl inside globals captured
  have sequence : Mutable.sequence (.ref address) heap = some (.ok (numbers (first :: tail)), heap) := by
    simp [Mutable.sequence, found]
  intro anchors stack
  apply Reaches.next rfl
  apply (Evaluates.arguments_reach (.cons (Evaluates.lookup bound) (.cons Evaluates.constant .nil))
    _ [] anchors stack).trans
  refine .next ?_ ((executed anchors (.generatorEnd :: stack)).trans (.next rfl .refl))
  simp [step, truthGeneratorStart, enumerateTarget, enumerateStart, run, sequence]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

private theorem bool_list (heap : Heap) (env : HeapCalls.Env) (address : Nat) (values : List Int)
    (globals : Mutable.Globals) (bound : env "rs" = some (.ref address))
    (found : heap[address]? = some (.list (numbers values))) :
    Evaluates program env boolExpression heap (flag (!values.isEmpty)) heap globals := by
  apply Evaluates.unary (value := flag values.isEmpty) (middle := heap)
  · apply Evaluates.unary (Evaluates.lookup bound)
    simp [HeapCalls.unary, Mutable.truth, found, numbers, flag]
  · rfl

/-- The lazy indexed-consecutive test examines exactly the elements required by all. -/
private theorem ordinary (heap : Heap) (env : HeapCalls.Env) (address : Nat) (values : List Int)
    (globals : Mutable.Globals) (bound : env "rs" = some (.ref address))
    (found : heap[address]? = some (.list (numbers values))) :
    Evaluates program env (.boolOp .and [boolExpression, allExpression]) heap
      (flag (!values.isEmpty && ProjectEulerSolutions.PokerStraights.consecutive values)) heap globals := by
  cases values with
  | nil =>
      exact Evaluates.boolean_stop (flag := false) (bool_list heap env address [] globals bound found) rfl rfl
  | cons first tail =>
      apply Evaluates.boolean_next (flag := true)
        (bool_list heap env address (first :: tail) globals bound found) rfl rfl
      exact Evaluates.boolean_last (flag := ProjectEulerSolutions.PokerStraights.consecutive (first :: tail))
        (all_enumerate heap env address first tail globals bound found) rfl

/-- For arbitrary integer lists the original Python straight test preserves every caller object. -/
theorem result (input : List Int) (heap : Heap) (address : Nat) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (numbers input))) :
    ReturnsValue program "is_straight" [.ref address] heap
      (flag (ProjectEulerSolutions.PokerStraights.referenceStraight (ScalarSort.ints input)))
      (heap ++ [.list (numbers (ScalarSort.ints input)), .list (numbers wheel)]) globals := by
  let firstHeap := heap ++ [Mutable.Object.list (numbers (ScalarSort.ints input))]
  let finalHeap := firstHeap ++ [Mutable.Object.list (numbers wheel)]
  let ready := setLocal (initial globals address) "rs" (.ref heap.length)
  have sortedFound : firstHeap[heap.length]? = some (.list (numbers (ScalarSort.ints input))) := by simp [firstHeap]
  have retained : finalHeap[heap.length]? = some (.list (numbers (ScalarSort.ints input))) := found_append sortedFound _
  have finished : ReturnsValue program "is_straight" [.ref address] heap
      (flag (ProjectEulerSolutions.PokerStraights.referenceStraight (ScalarSort.ints input))) finalHeap globals := by
    apply BlockReturns.function rfl rfl
    apply BlockReturns.assign
      (Evaluates.call (.cons (Evaluates.lookup (get_rs globals address)) .nil)
        (sorted_ranks.result (globals := globals) input heap address found))
    apply BlockReturns.branch (flag := decide (ScalarSort.ints input = wheel))
      (value := flag (decide (ScalarSort.ints input = wheel))) (middle := finalHeap)
      (wheel_test firstHeap ready heap.length (ScalarSort.ints input) globals rfl sortedFound) rfl
    by_cases same : ScalarSort.ints input = wheel
    · simp only [same, decide_true, if_true]
      apply BlockReturns.return_value
      simpa [ProjectEulerSolutions.PokerStraights.referenceStraight, same] using
        (Evaluates.constant : Evaluates program ready (.constant (.bool true)) finalHeap (flag true) finalHeap globals)
    · simp only [same, decide_false]
      apply BlockReturns.return_value
      simpa [ProjectEulerSolutions.PokerStraights.referenceStraight, same] using
        ordinary finalHeap ready heap.length (ScalarSort.ints input) globals rfl retained
  simpa only [firstHeap, finalHeap, List.append_assoc] using finished

theorem «Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "is_straight" [.ref address] heap).Returns := by
  obtain ⟨input, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (result input heap address [] found).returns

theorem «ReturnType» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "is_straight" [.ref address] heap).ReturnType "bool" := by
  obtain ⟨input, found⟩ := Mutable.Value.ints_of_hasType typed
  exact .inr ⟨flag (ProjectEulerSolutions.PokerStraights.referenceStraight (ScalarSort.ints input)), [], _, heap.length,
    (result input heap address [] found).finishes, rfl⟩

theorem «Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "is_straight" [.ref address] heap).Supported :=
  («Returns» heap address valid typed).supported

end data.«project-euler-statements».data.py.project_euler_statements.p54.is_straight

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.flush_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
set_option Elab.async false

private abbrev program := P54Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev text (value : String) : Mutable.Value := .scalar (.string value)
private abbrev texts (values : List String) : List Mutable.Value := values.map text
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)

/-- Only the two indexed Unicode characters are constrained; suffixes are arbitrary. -/
structure Card where
  token : String
  rankChar : Char
  suitChar : Char
  suffix : List Char
  shape : token.toList = rankChar :: suitChar :: suffix

def tokens (cards : List Card) : List Mutable.Value := cards.map (fun card => text card.token)
def suits (cards : List Card) : List String := cards.map (fun card => String.singleton card.suitChar)

private theorem found_append {heap : Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem suit_item (card : Card) (heap : Heap) :
    Mutable.getItem (text card.token) (number 1) heap =
      some (.ok (text (String.singleton card.suitChar)), heap) := by
  have inside : ¬ (card.suffix.length : Int)+1+1 ≤ 1 := by omega
  simp [Mutable.getItem, Strings.get, FormalSW.Py.Builtin.Sequence.get?,
    FormalSW.Py.Builtin.Sequence.normalizeIndex, card.shape, text, inside]

private abbrev suitExpression : Expr := .subscript (.name "c") (.constant (.int 1))

private theorem suit_eval (heap : Heap) (env : HeapCalls.Env) (card : Card) (globals : Mutable.Globals)
    (bound : env "c" = some (text card.token)) :
    Evaluates program env suitExpression heap (text (String.singleton card.suitChar)) heap globals := by
  exact Evaluates.subscript (by intros; simp) (Evaluates.lookup bound) Evaluates.constant (suit_item card heap)

private theorem collect_suits (heap : Heap) (address : Nat) (cards remaining : List Card)
    (found : heap[address]? = some (.list (tokens cards))) (position : Nat)
    (suffix : cards.drop position = remaining) (collected : List Mutable.Value)
    (env : HeapCalls.Env) (globals : Mutable.Globals) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "c" (.ref address) position [.comprehensionAppend heap.length suitExpression] []]
      (heap ++ [.list collected]) finalEnv (heap ++ [.list (collected ++ texts (suits remaining))]) globals := by
  have sequence (done : List Mutable.Value) :
      Mutable.sequence (.ref address) (heap ++ [.list done]) = some (.ok (tokens cards), heap ++ [.list done]) := by
    have original := found_append found [.list done]
    simp [Mutable.sequence, original]
  induction remaining generalizing position env collected with
  | nil =>
      have missing : cards[position]? = none := by
        simpa [suffix] using (List.head?_drop (l := cards) (i := position)).symm
      have absent : (tokens cards)[position]? = none := by
        simp only [tokens, List.getElem?_map, missing, Option.map_none]
      refine ⟨env, ?_⟩
      apply BlockContinues.sequence_done (source := .ref address) (sequence collected) absent
      simpa only [suits, List.map_nil, texts, List.append_nil] using
        (BlockContinues.nil (module := program) (env := env) (heap := heap ++ [.list collected]) (globals := globals))
  | cons card rest ih =>
      have item : cards[position]? = some card := by
        simpa [suffix] using (List.head?_drop (l := cards) (i := position)).symm
      let ready := setLocal env "c" (text card.token)
      have emitted : BlockContinues program ready [.comprehensionAppend heap.length suitExpression]
          (heap ++ [.list collected]) ready
          (heap ++ [.list (collected ++ [text (String.singleton card.suitChar)])]) globals := by
        have appended := BlockContinues.comprehension_append (module := program) (env := ready) (globals := globals)
          (address := heap.length) (heap := heap ++ [.list collected]) (items := collected)
          (suit_eval (heap ++ [.list collected]) ready card globals rfl) (by simp)
        simpa using appended
      obtain ⟨finalEnv, continued⟩ := ih (position+1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix])
        (collected ++ [text (String.singleton card.suitChar)]) ready
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.sequence_step (source := .ref address) (value := text card.token) (sequence collected)
        (by simp only [tokens, List.getElem?_map, item, Option.map_some])
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, suits, texts, List.append_assoc] using
        emitted.append continued

namespace hand_suits
private abbrev params := ((findFunctionIn program.body "hand_suits").getD ([], [])).1
private abbrev body := ((findFunctionIn program.body "hand_suits").getD ([], [])).2
private abbrev initial (globals : Mutable.Globals) (address : Nat) : HeapCalls.Env := functionEnv params body [.ref address] globals
private theorem get_hand (globals : Mutable.Globals) (address : Nat) : initial globals address "hand" = some (.ref address) := by
  cases globals <;> rfl

/-- The original c[1] comprehension creates one fresh suit list and preserves its input. -/
theorem result (cards : List Card) (heap : Heap) (address : Nat) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (tokens cards))) :
    ReturnsValue program "hand_suits" [.ref address] heap (.ref heap.length)
      (heap ++ [.list (texts (suits cards))]) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  obtain ⟨finalEnv, collected⟩ := collect_suits heap address cards cards found 0 rfl []
    (comprehensionEnv (initial globals address) [("c", .name "hand", [])]) globals
  apply Evaluates.list_comp_sequence (name := "c") (iterable := .name "hand") (filters := []) (generators := [])
    (finalEnv := finalEnv) (items := tokens cards) (value := .ref address) (middle := heap)
    (by intro expressions impossible; cases impossible) (Evaluates.lookup (get_hand globals address))
    (by simp [Mutable.sequence, found])
  simpa only [List.nil_append, comprehensionFilters, comprehensionBody, List.foldr_nil] using collected
end hand_suits

private abbrev firstSuit : Expr := .subscript (.name "suits") (.constant (.int 0))
private abbrev tailSuits : Expr := .subscript (.name "suits") (.slice (some (.constant (.int 1))) none none)
private abbrev equalSuit : Expr := .compare (.name "s") [(.eq, firstSuit)]
private abbrev allSuits : Expr := .consumeGenerator (.builtinCall .all []) equalSuit [(.name "s", tailSuits, [])]
private abbrev boolSuits : Expr := .unaryOp .not (.unaryOp .not (.name "suits"))

private theorem equal_eval (heap : Heap) (env : HeapCalls.Env) (address : Nat) (first value : String)
    (tail : List String) (globals : Mutable.Globals)
    (bound : env "suits" = some (.ref address)) (found : heap[address]? = some (.list (texts (first :: tail))))
    (getValue : env "s" = some (text value)) :
    Evaluates program env equalSuit heap (flag (decide (value = first))) heap globals := by
  apply Evaluates.compare (av := text value) (bv := text first) (middle := heap) (afterRight := heap)
    (Evaluates.lookup getValue)
  · apply Evaluates.subscript (by intros; simp) (Evaluates.lookup bound) Evaluates.constant
    simpa only [texts, List.map_cons] using Mutable.getItem_list heap address 0 (texts (first :: tail)) found (by simp [texts])
  · simp [HeapCalls.compare, scalarCompare, flag]

private theorem all_loop (heap : Heap) (suitsAddress tailAddress : Nat) (first : String) (tail remaining : List String)
    (original : heap[suitsAddress]? = some (.list (texts (first :: tail))))
    (sliceFound : heap[tailAddress]? = some (.list (texts tail))) (position : Nat)
    (suffix : tail.drop position = remaining) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (bound : env "suits" = some (.ref suitsAddress)) :
    BlockReturns program env
      [.sequenceStepLoop "s" (.ref tailAddress) position (truthBody true equalSuit) [], .return (.constant (.bool true))]
      heap (flag (remaining.all (fun value => decide (value = first)))) heap globals := by
  have sequence : Mutable.sequence (.ref tailAddress) heap = some (.ok (texts tail), heap) := by
    simp [Mutable.sequence, sliceFound]
  induction remaining generalizing position env with
  | nil =>
      have missing : tail[position]? = none := by simpa [suffix] using (List.head?_drop (l := tail) (i := position)).symm
      apply BlockReturns.sequence_done (source := .ref tailAddress) sequence
        (by simp only [texts, List.getElem?_map, missing, Option.map_none])
      exact BlockReturns.return_value Evaluates.constant
  | cons value rest ih =>
      have item : tail[position]? = some value := by simpa [suffix] using (List.head?_drop (l := tail) (i := position)).symm
      let ready := setLocal env "s" (text value)
      have captured : ready "suits" = some (.ref suitsAddress) := by simpa [ready, setLocal] using bound
      have tested := equal_eval heap ready suitsAddress first value tail globals captured original rfl
      apply BlockReturns.sequence_step (source := .ref tailAddress) (value := text value) sequence
        (by simp only [texts, List.getElem?_map, item, Option.map_some])
      cases accepted : decide (value = first) with
      | false =>
          simp only [List.all_cons, accepted, Bool.false_and]
          apply BlockReturns.branch (flag := false) (by simpa only [accepted] using tested) rfl
          exact BlockReturns.return_value Evaluates.constant
      | true =>
          simp only [List.all_cons, accepted, Bool.true_and]
          apply BlockReturns.branch (flag := true) (by simpa only [accepted] using tested) rfl
          have continued := ih (position+1) (by simp [List.drop_add_one_eq_tail_drop, suffix]) ready captured
          simpa [truthBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using continued

private theorem all_eval (heap : Heap) (env : HeapCalls.Env) (address : Nat) (first : String) (tail : List String)
    (globals : Mutable.Globals) (bound : env "suits" = some (.ref address))
    (found : heap[address]? = some (.list (texts (first :: tail)))) :
    Evaluates program env allSuits heap (flag (tail.all (fun value => decide (value = first))))
      (heap ++ [.list (texts tail)]) globals := by
  have sliced : Evaluates program env tailSuits heap (.ref heap.length) (heap ++ [.list (texts tail)]) globals := by
    apply Evaluates.slice (.cons (Evaluates.lookup bound) (.cons Evaluates.constant
      (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
    simpa only [texts, List.map_cons] using Mutable.getSlice_list_suffix heap address (texts (first :: tail)) 1 found
  let afterSlice := heap ++ [Mutable.Object.list (texts tail)]
  let inside := comprehensionTargetsEnv env [(.name "s", tailSuits, [])]
  have captured : inside "suits" = some (.ref address) := by
    simpa [inside, comprehensionTargetsEnv, targetLocals] using bound
  have retained : afterSlice[address]? = some (.list (texts (first :: tail))) := found_append found _
  have sliceFound : afterSlice[heap.length]? = some (.list (texts tail)) := by simp [afterSlice]
  have executed := all_loop afterSlice address heap.length first tail tail retained sliceFound 0 rfl inside globals captured
  apply Evaluates.truth_generator_sequence (universal := true) (target := .name "s") (iterable := tailSuits)
    (filters := []) (generators := []) (items := texts tail) (source := .ref heap.length) (middle := afterSlice)
    (by intro expressions impossible; cases impossible) (by intro expressions impossible; cases impossible)
    (by intro expressions impossible; cases impossible) sliced (by simp [Mutable.sequence, sliceFound])
  exact executed

def flush (values : List String) : Bool :=
  match values with | [] => false | first :: tail => tail.all (fun value => decide (value = first))

namespace is_flush
private abbrev params := ((findFunctionIn program.body "is_flush").getD ([], [])).1
private abbrev body := ((findFunctionIn program.body "is_flush").getD ([], [])).2
private abbrev initial (globals : Mutable.Globals) (address : Nat) : HeapCalls.Env := functionEnv params body [.ref address] globals
private theorem get_hand (globals : Mutable.Globals) (address : Nat) : initial globals address "hand" = some (.ref address) := by
  cases globals <;> rfl

private theorem bool_eval (heap : Heap) (env : HeapCalls.Env) (address : Nat) (values : List String)
    (globals : Mutable.Globals) (bound : env "suits" = some (.ref address))
    (found : heap[address]? = some (.list (texts values))) :
    Evaluates program env boolSuits heap (flag (!values.isEmpty)) heap globals := by
  apply Evaluates.unary (value := flag values.isEmpty) (middle := heap)
  · apply Evaluates.unary (Evaluates.lookup bound)
    simp [HeapCalls.unary, Mutable.truth, found, texts, flag]
  · rfl

/-- The original source short circuits empty hands and checks the sliced suit suffix lazily. -/
theorem result (cards : List Card) (heap : Heap) (address : Nat) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (tokens cards))) :
    ∃ extra : Heap, ReturnsValue program "is_flush" [.ref address] heap (flag (flush (suits cards))) (heap ++ extra) globals := by
  let afterSuits := heap ++ [Mutable.Object.list (texts (suits cards))]
  let ready := setLocal (initial globals address) "suits" (.ref heap.length)
  have suitsFound : afterSuits[heap.length]? = some (.list (texts (suits cards))) := by simp [afterSuits]
  cases shape : suits cards with
  | nil =>
      refine ⟨[.list []], ?_⟩
      have returned : ReturnsValue program "is_flush" [.ref address] heap (flag false) afterSuits globals := by
        apply BlockReturns.function rfl rfl
        apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup (get_hand globals address)) .nil)
          (hand_suits.result cards heap address globals found))
        apply BlockReturns.return_value
        exact Evaluates.boolean_stop (flag := false) (value := flag false) (middle := afterSuits)
          (by simpa only [afterSuits, shape, List.isEmpty_nil, Bool.not_true] using bool_eval afterSuits ready heap.length (suits cards) globals rfl suitsFound) rfl rfl
      simpa only [flush, shape, afterSuits, texts, List.map_nil] using returned
  | cons first tail =>
      refine ⟨[.list (texts (first :: tail)), .list (texts tail)], ?_⟩
      have returned : ReturnsValue program "is_flush" [.ref address] heap
          (flag (tail.all (fun value => decide (value = first)))) (afterSuits ++ [.list (texts tail)]) globals := by
        apply BlockReturns.function rfl rfl
        apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup (get_hand globals address)) .nil)
          (hand_suits.result cards heap address globals found))
        apply BlockReturns.return_value
        apply Evaluates.boolean_next (flag := true) (value := flag true) (middle := afterSuits)
          (by simpa only [afterSuits, shape, List.isEmpty_cons, Bool.not_false] using bool_eval afterSuits ready heap.length (suits cards) globals rfl suitsFound) rfl rfl
        exact Evaluates.boolean_last (flag := tail.all (fun value => decide (value = first)))
          (all_eval afterSuits ready heap.length first tail globals rfl (by simpa only [shape] using suitsFound)) rfl
      simpa only [flush, shape, afterSuits, List.append_assoc] using returned
end is_flush

end data.«project-euler-statements».data.py.project_euler_statements.p54.flush_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.rank_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
set_option Elab.async false

private abbrev program := P54Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev text (value : String) : Mutable.Value := .scalar (.string value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)

private theorem found_append {heap : Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

namespace rank_value
private abbrev params := ((findFunctionIn program.body "rank_value").getD ([], [])).1
private abbrev body := ((findFunctionIn program.body "rank_value").getD ([], [])).2
private abbrev initial (globals : Mutable.Globals) (value : Mutable.Value) : HeapCalls.Env :=
  functionEnv params body [value] globals
private theorem get_rank (globals : Mutable.Globals) (value : Mutable.Value) :
    initial globals value "rank" = some value := by cases globals <;> rfl

/-- The actual isinstance(..., int) branch returns its integer argument without reading the table. -/
theorem result_int (rank : Int) (heap : Heap) (globals : Mutable.Globals) :
    ReturnsValue program "rank_value" [number rank] heap (number rank) heap globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (flag := true) (value := flag true) (middle := heap)
  · exact Evaluates.builtin (.cons (Evaluates.lookup (get_rank globals (number rank))) .nil) rfl
  · rfl
  · exact Evaluates.lookup (get_rank globals (number rank))

/-- The string branch reads the live caller-provided rank_values dictionary. -/
theorem result_lookup (rank : String) (heap : Heap) (globals : Mutable.Globals) (address : Nat)
    (entries : List (Constant × Mutable.Value)) (value : Mutable.Value)
    (getTable : globals.lookup "rank_values" = some (.ref address))
    (found : heap[address]? = some (.dict entries))
    (present : ScalarDict.lookup entries (.string rank) = some value) :
    ReturnsValue program "rank_value" [text rank] heap value heap globals := by
  have table : initial globals (text rank) "rank_values" = some (.ref address) := by
    cases globals with
    | nil => simp at getTable
    | cons first rest => exact getTable
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (flag := false) (value := flag false) (middle := heap)
  · exact Evaluates.builtin (.cons (Evaluates.lookup (get_rank globals (text rank))) .nil) rfl
  · rfl
  · apply Evaluates.subscript (by intros; simp) (Evaluates.lookup table)
      (Evaluates.lookup (get_rank globals (text rank)))
    exact Mutable.getItem_dictionary heap address entries found (.string rank) present
end rank_value

private abbrev Card := flush_source.Card

def ranks (cards : List Card) (valuation : Card → Int) : List Mutable.Value :=
  cards.map (fun card => number (valuation card))

private theorem first_item (card : Card) (heap : Heap) :
    Mutable.getItem (text card.token) (number 0) heap =
      some (.ok (text (String.singleton card.rankChar)), heap) := by
  have inside : ¬ (card.suffix.length : Int)+1+1 ≤ 0 := by omega
  simp [Mutable.getItem, Strings.get, FormalSW.Py.Builtin.Sequence.get?,
    FormalSW.Py.Builtin.Sequence.normalizeIndex, card.shape, text, inside]

private abbrev rankExpression : Expr :=
  .call (.name "rank_value") [.subscript (.name "c") (.constant (.int 0))]

private theorem rank_eval (heap : Heap) (env : HeapCalls.Env) (card : Card) (value : Int)
    (globals : Mutable.Globals) (tableAddress : Nat) (entries : List (Constant × Mutable.Value))
    (bound : env "c" = some (text card.token))
    (getTable : globals.lookup "rank_values" = some (.ref tableAddress))
    (found : heap[tableAddress]? = some (.dict entries))
    (present : ScalarDict.lookup entries (.string (String.singleton card.rankChar)) = some (number value)) :
    Evaluates program env rankExpression heap (number value) heap globals := by
  have indexed : Evaluates program env (.subscript (.name "c") (.constant (.int 0))) heap
      (text (String.singleton card.rankChar)) heap globals :=
    Evaluates.subscript (by intros; simp) (Evaluates.lookup bound) Evaluates.constant (first_item card heap)
  exact Evaluates.call (.cons indexed .nil)
    (rank_value.result_lookup (String.singleton card.rankChar) heap globals tableAddress entries (number value) getTable found present)

private theorem collect_ranks (heap : Heap) (address tableAddress : Nat) (cards remaining : List Card)
    (valuation : Card → Int) (entries : List (Constant × Mutable.Value))
    (found : heap[address]? = some (.list (flush_source.tokens cards)))
    (tableFound : heap[tableAddress]? = some (.dict entries))
    (position : Nat) (suffix : cards.drop position = remaining) (collected : List Mutable.Value)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getTable : globals.lookup "rank_values" = some (.ref tableAddress))
    (present : ∀ card ∈ cards, ScalarDict.lookup entries (.string (String.singleton card.rankChar)) = some (number (valuation card))) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "c" (.ref address) position [.comprehensionAppend heap.length rankExpression] []]
      (heap ++ [.list collected]) finalEnv (heap ++ [.list (collected ++ ranks remaining valuation)]) globals := by
  have sequence (done : List Mutable.Value) :
      Mutable.sequence (.ref address) (heap ++ [.list done]) =
        some (.ok (flush_source.tokens cards), heap ++ [.list done]) := by
    have original := found_append found [.list done]
    simp [Mutable.sequence, original]
  induction remaining generalizing position env collected with
  | nil =>
      have missing : cards[position]? = none := by
        simpa [suffix] using (List.head?_drop (l := cards) (i := position)).symm
      have absent : (flush_source.tokens cards)[position]? = none := by
        simp only [flush_source.tokens, List.getElem?_map, missing, Option.map_none]
      refine ⟨env, ?_⟩
      apply BlockContinues.sequence_done (source := .ref address) (sequence collected) absent
      simpa only [ranks, List.map_nil, List.append_nil] using
        (BlockContinues.nil (module := program) (env := env) (heap := heap ++ [.list collected]) (globals := globals))
  | cons card rest ih =>
      have item : cards[position]? = some card := by
        simpa [suffix] using (List.head?_drop (l := cards) (i := position)).symm
      let ready := setLocal env "c" (text card.token)
      have extendedTable : (heap ++ [.list collected])[tableAddress]? = some (.dict entries) := found_append tableFound _
      have valued := rank_eval (heap ++ [.list collected]) ready card (valuation card) globals tableAddress entries rfl
        getTable extendedTable (present card (List.mem_of_getElem? item))
      have emitted : BlockContinues program ready [.comprehensionAppend heap.length rankExpression]
          (heap ++ [.list collected]) ready (heap ++ [.list (collected ++ [number (valuation card)])]) globals := by
        have appended := BlockContinues.comprehension_append (module := program) (env := ready) (globals := globals)
          (address := heap.length) (heap := heap ++ [.list collected]) (items := collected) valued (by simp)
        simpa using appended
      obtain ⟨finalEnv, continued⟩ := ih (position+1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) (collected ++ [number (valuation card)]) ready
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.sequence_step (source := .ref address) (value := text card.token) (sequence collected)
        (by simp only [flush_source.tokens, List.getElem?_map, item, Option.map_some])
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, ranks, List.append_assoc] using
        emitted.append continued

namespace hand_ranks
private abbrev params := ((findFunctionIn program.body "hand_ranks").getD ([], [])).1
private abbrev body := ((findFunctionIn program.body "hand_ranks").getD ([], [])).2
private abbrev initial (globals : Mutable.Globals) (address : Nat) : HeapCalls.Env :=
  functionEnv params body [.ref address] globals
private theorem get_hand (globals : Mutable.Globals) (address : Nat) : initial globals address "hand" = some (.ref address) := by
  cases globals <;> rfl

/-- The original c[0]/rank_value comprehension uses the live rank dictionary and creates one fresh list. -/
theorem result (cards : List Card) (valuation : Card → Int) (heap : Heap) (address tableAddress : Nat)
    (entries : List (Constant × Mutable.Value)) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (flush_source.tokens cards)))
    (tableFound : heap[tableAddress]? = some (.dict entries))
    (getTable : globals.lookup "rank_values" = some (.ref tableAddress))
    (present : ∀ card ∈ cards, ScalarDict.lookup entries (.string (String.singleton card.rankChar)) = some (number (valuation card))) :
    ReturnsValue program "hand_ranks" [.ref address] heap (.ref heap.length)
      (heap ++ [.list (ranks cards valuation)]) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  obtain ⟨finalEnv, collected⟩ := collect_ranks heap address tableAddress cards cards valuation entries found tableFound
    0 rfl [] (comprehensionEnv (initial globals address) [("c", .name "hand", [])]) globals getTable present
  apply Evaluates.list_comp_sequence (name := "c") (iterable := .name "hand") (filters := []) (generators := [])
    (finalEnv := finalEnv) (items := flush_source.tokens cards) (value := .ref address) (middle := heap)
    (by intro expressions impossible; cases impossible) (Evaluates.lookup (get_hand globals address))
    (by simp [Mutable.sequence, found])
  simpa only [List.nil_append, comprehensionFilters, comprehensionBody, List.foldr_nil] using collected
end hand_ranks

end data.«project-euler-statements».data.py.project_euler_statements.p54.rank_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.counts_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.PokerUnique
set_option Elab.async false

private abbrev program := P54Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev numbers (values : List Int) : List Mutable.Value := values.map number
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev buffer (heap : Heap) (values : List Int) : Heap := heap ++ [.list (numbers values)]
private abbrev working := ProjectEulerSolutions.HeapCollection.working

private theorem found_append {heap : Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private abbrev dedupBody : List Stmt :=
  [.ifThen (.membership (.name "r") (.name "vals") true)
    [.expr (.call (.attribute (.name "vals") "append") [.name "r"])] []]

private theorem dedup_step (heap : Heap) (env : HeapCalls.Env) (done : List Int) (value : Int)
    (globals : Mutable.Globals) (getValue : env "r" = some (number value))
    (getVals : env "vals" = some (.ref heap.length)) :
    BlockContinues program env dedupBody (buffer heap done) env (buffer heap (addUnique done value)) globals := by
  have found : (buffer heap done)[heap.length]? = some (.list (numbers done)) := by simp [buffer]
  have tested : Evaluates program env (.membership (.name "r") (.name "vals") true) (buffer heap done)
      (flag (!decide (value ∈ done))) (buffer heap done) globals := by
    apply Evaluates.membership (.cons (Evaluates.lookup getValue) (.cons (Evaluates.lookup getVals) .nil))
    exact membership_list_ints (buffer heap done) heap.length value done found true
  by_cases present : value ∈ done
  · simp only [addUnique, if_pos present]
    apply BlockContinues.branch (flag := false) (value := flag false) (middle := buffer heap done)
      (by simpa only [present, decide_true, Bool.not_true] using tested) rfl
    exact BlockContinues.nil
  · simp only [addUnique, if_neg present]
    apply BlockContinues.branch (flag := true) (value := flag true) (middle := buffer heap done)
      (by simpa only [present, decide_false, Bool.not_false] using tested) rfl
    apply BlockContinues.discard
    have appended := Evaluates.append (module := program) (env := env) (globals := globals)
      (Evaluates.lookup getVals) found (Evaluates.lookup getValue) found
    simpa [buffer, numbers, List.map_append, List.set_append_right] using appended

private theorem dedup_loop (heap : Heap) (address : Nat) (values remaining : List Int)
    (found : heap[address]? = some (.list (numbers values))) (position : Nat)
    (suffix : values.drop position = remaining) (done : List Int) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getRs : env "rs" = some (.ref address)) (getVals : env "vals" = some (.ref heap.length)) :
    ∃ finalEnv, finalEnv "rs" = some (.ref address) ∧ finalEnv "vals" = some (.ref heap.length) ∧
      BlockContinues program env [.sequenceStepLoop "r" (.ref address) position dedupBody []]
        (buffer heap done) finalEnv (buffer heap (remaining.foldl addUnique done)) globals := by
  have sequence (collected : List Int) : Mutable.sequence (.ref address) (buffer heap collected) =
      some (.ok (numbers values), buffer heap collected) := by
    have original := found_append found [.list (numbers collected)]
    simp [Mutable.sequence, original, buffer]
  induction remaining generalizing position done env with
  | nil =>
      have missing : values[position]? = none := by simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      refine ⟨env, getRs, getVals, ?_⟩
      apply BlockContinues.sequence_done (source := .ref address) (sequence done)
        (by simp only [numbers, List.getElem?_map, missing, Option.map_none])
      exact BlockContinues.nil
  | cons value rest ih =>
      have item : values[position]? = some value := by simpa [suffix] using (List.head?_drop (l := values) (i := position)).symm
      let ready := setLocal env "r" (number value)
      have readyRs : ready "rs" = some (.ref address) := by simpa [ready, setLocal] using getRs
      have readyVals : ready "vals" = some (.ref heap.length) := by simpa [ready, setLocal] using getVals
      have stepped := dedup_step heap ready done value globals rfl readyVals
      obtain ⟨finalEnv, finalRs, finalVals, continued⟩ := ih (position+1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) (addUnique done value) ready readyRs readyVals
      refine ⟨finalEnv, finalRs, finalVals, ?_⟩
      apply BlockContinues.sequence_step (source := .ref address) (value := number value) (sequence done)
        (by simp only [numbers, List.getElem?_map, item, Option.map_some])
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, List.foldl_cons] using
        stepped.append continued

/-- One fresh tuple contains the occurrence count followed by its first-seen rank. -/
def row (values : List Int) (rank : Int) : Mutable.Object := .tuple [number (values.count rank), number rank]
def scratch (values keys : List Int) : Heap := keys.map (row values)
def references (start : Nat) : List Int → List Mutable.Value
  | [] => []
  | _ :: rest => .ref start :: references (start+1) rest

private abbrev countExpression : Expr := .call (.attribute (.name "rs") "count") [.name "v"]
private abbrev rowExpression : Expr := .tuple [countExpression, .name "v"]

private theorem row_eval (heap : Heap) (env : HeapCalls.Env) (address : Nat) (values : List Int) (rank : Int)
    (globals : Mutable.Globals) (getRs : env "rs" = some (.ref address)) (getRank : env "v" = some (number rank))
    (found : heap[address]? = some (.list (numbers values))) :
    Evaluates program env rowExpression heap (.ref heap.length) (heap ++ [row values rank]) globals := by
  have counted : Evaluates program env countExpression heap (number (values.count rank)) heap globals := by
    apply Evaluates.count (Evaluates.lookup getRs) found (.cons (Evaluates.lookup getRank) .nil)
      (primitive_count_list heap address values rank found)
    intro name same
    cases same
    simp only [getRs, Option.isSome_some]
  exact Evaluates.tuple (.cons counted (.cons (Evaluates.lookup getRank) .nil)) (by simp)

private theorem collect_rows (base : Heap) (address valsAddress : Nat) (values keys remaining : List Int)
    (found : base[address]? = some (.list (numbers values)))
    (valsFound : base[valsAddress]? = some (.list (numbers keys))) (position : Nat)
    (suffix : keys.drop position = remaining) (groups : List Mutable.Value) (garbage : Heap)
    (env : HeapCalls.Env) (globals : Mutable.Globals) (getRs : env "rs" = some (.ref address)) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "v" (.ref valsAddress) position [.comprehensionAppend base.length rowExpression] []]
      (working base groups garbage) finalEnv
      (working base (groups ++ references (working base groups garbage).length remaining)
        (garbage ++ scratch values remaining)) globals := by
  have sequence (collected : List Mutable.Value) (extra : Heap) :
      Mutable.sequence (.ref valsAddress) (working base collected extra) =
        some (.ok (numbers keys), working base collected extra) := by
    have retained := found_append valsFound (.list collected :: extra)
    simp [Mutable.sequence, ProjectEulerSolutions.HeapCollection.working, retained]
  induction remaining generalizing position groups garbage env with
  | nil =>
      have missing : keys[position]? = none := by simpa [suffix] using (List.head?_drop (l := keys) (i := position)).symm
      refine ⟨env, ?_⟩
      apply BlockContinues.sequence_done (source := .ref valsAddress) (sequence groups garbage)
        (by simp only [numbers, List.getElem?_map, missing, Option.map_none])
      simpa only [references, scratch, List.map_nil, List.append_nil] using
        (BlockContinues.nil (module := program) (env := env) (heap := working base groups garbage) (globals := globals))
  | cons rank rest ih =>
      have item : keys[position]? = some rank := by simpa [suffix] using (List.head?_drop (l := keys) (i := position)).symm
      let ready := setLocal env "v" (number rank)
      have readyRs : ready "rs" = some (.ref address) := by simpa [ready, setLocal] using getRs
      have original : (working base groups garbage)[address]? = some (.list (numbers values)) :=
        found_append found (.list groups :: garbage)
      have tuple := row_eval (working base groups garbage) ready address values rank globals readyRs rfl original
      have emitted := ProjectEulerSolutions.HeapCollection.emit base groups garbage [row values rank]
        (.ref (working base groups garbage).length) tuple
      obtain ⟨finalEnv, continued⟩ := ih (position+1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix])
        (groups ++ [.ref (working base groups garbage).length]) (garbage ++ [row values rank]) ready readyRs
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.sequence_step (source := .ref valsAddress) (value := number rank) (sequence groups garbage)
        (by simp only [numbers, List.getElem?_map, item, Option.map_some])
      have lengthStep :
          (working base (groups ++ [.ref (working base groups garbage).length]) (garbage ++ [row values rank])).length =
            (working base groups garbage).length+1 := by
        simp [ProjectEulerSolutions.HeapCollection.working]
        omega
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, references, scratch,
        List.append_assoc, lengthStep] using emitted.append continued

private abbrev params := ((findFunctionIn program.body "rank_counts").getD ([], [])).1
private abbrev body := ((findFunctionIn program.body "rank_counts").getD ([], [])).2
private abbrev initial (globals : Mutable.Globals) (address : Nat) : HeapCalls.Env :=
  functionEnv params body [.ref address] globals
private theorem get_rs (globals : Mutable.Globals) (address : Nat) : initial globals address "rs" = some (.ref address) := by
  cases globals <;> rfl

/-- The returned list references one count/rank tuple per first-seen rank, preserving the caller heap. -/
theorem result (values : List Int) (heap : Heap) (address : Nat) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (numbers values))) :
    ReturnsValue program "rank_counts" [.ref address] heap (.ref (heap.length+1))
      (heap ++ [.list (numbers (unique values)), .list (references (heap.length+2) (unique values))] ++
        scratch values (unique values)) globals := by
  let ready := setLocal (initial globals address) "vals" (.ref heap.length)
  have readyRs : ready "rs" = some (.ref address) := by simpa [ready, setLocal] using get_rs globals address
  obtain ⟨deduped, getRs, getVals, dedupedLoop⟩ := dedup_loop heap address values values found 0 rfl [] ready globals readyRs rfl
  let base := buffer heap (unique values)
  have sourceFound : base[address]? = some (.list (numbers values)) := found_append found _
  have valsFound : base[heap.length]? = some (.list (numbers (unique values))) := by simp [base, buffer]
  let inside := comprehensionEnv deduped [("v", .name "vals", [])]
  have insideRs : inside "rs" = some (.ref address) := by
    simpa [inside, comprehensionEnv] using getRs
  obtain ⟨finalEnv, collected⟩ := collect_rows base address heap.length values (unique values) (unique values)
    sourceFound valsFound 0 rfl [] [] inside globals insideRs
  have built : Evaluates program deduped (.listComp rowExpression [("v", .name "vals", [])]) base (.ref base.length)
      (working base (references (base.length+1) (unique values)) (scratch values (unique values))) globals := by
    apply Evaluates.list_comp_sequence (name := "v") (iterable := .name "vals") (filters := []) (generators := [])
      (finalEnv := finalEnv) (items := numbers (unique values)) (value := .ref heap.length) (middle := base)
      (by intro expressions impossible; cases impossible) (Evaluates.lookup getVals)
      (by simp [Mutable.sequence, valsFound])
    simpa only [List.nil_append, comprehensionFilters, comprehensionBody, List.foldr_nil,
      ProjectEulerSolutions.HeapCollection.working, List.length_append, List.length_singleton] using collected
  have returned : ReturnsValue program "rank_counts" [.ref address] heap (.ref base.length)
      (working base (references (base.length+1) (unique values)) (scratch values (unique values))) globals := by
    apply BlockReturns.function rfl rfl
    apply BlockReturns.assign (Evaluates.list .nil)
    apply BlockContinues.returns
      (body := [.forIn (.name "r") (.name "rs") dedupBody []])
      (following := [.return (.listComp rowExpression [("v", .name "vals", [])])])
      (middleEnv := deduped) (middleHeap := base)
    · apply BlockContinues.for_sequence (items := numbers values) (by intro expressions impossible; cases impossible)
        (Evaluates.lookup readyRs) (by simp [Mutable.sequence, found_append found [.list []]])
      exact dedupedLoop
    · exact BlockReturns.return_value built
  simpa only [base, buffer, ProjectEulerSolutions.HeapCollection.working, unique, List.length_append,
    List.length_singleton, List.append_assoc, List.cons_append, List.nil_append, Nat.add_assoc] using returned

end data.«project-euler-statements».data.py.project_euler_statements.p54.counts_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.rank_counts
open FormalSW.PyAst

theorem «Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call P54Ast.module "rank_counts" [.ref address] heap).Returns := by
  obtain ⟨values, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (counts_source.result values heap address [] found).returns

theorem «Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call P54Ast.module "rank_counts" [.ref address] heap).Supported :=
  («Returns» heap address valid typed).supported

end data.«project-euler-statements».data.py.project_euler_statements.p54.rank_counts

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.sort_counts_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

private abbrev program := P54Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev numbers (values : List Int) : List Mutable.Value := values.map number

structure Entry where
  address : Nat
  count : Int
  rank : Int

def Entry.pair (entry : Entry) : Int × Int := (entry.count, entry.rank)
def original (entry : Entry) : Mutable.Value := .ref entry.address
def items (entries : List Entry) : List Mutable.Value := entries.map original
def row (entry : Entry) : Mutable.Object := .tuple [number entry.count, number entry.rank]
def keyRow (entry : Entry) : Mutable.Object := .tuple [number (-entry.count), number (-entry.rank)]
def scratch (entries : List Entry) : Heap := entries.map keyRow

def Found (heap : Heap) (entries : List Entry) : Prop :=
  ∀ entry ∈ entries, heap[entry.address]? = some (row entry)

def cached (start : Nat) : List Entry → List (Mutable.Value × Mutable.Value)
  | [] => []
  | entry :: rest => (original entry, .ref start) :: cached (start+1) rest

def readPair (heap : Heap) (value : Mutable.Value) : Int × Int :=
  let values := TupleSorting.readInts heap value
  (values.getD 0 0, values.getD 1 0)

def negative (pair : Int × Int) : Int × Int := (-pair.1, -pair.2)
def negativeLess (left right : Int × Int) : Bool := PokerGroupOrder.pairLess (negative left) (negative right)
def less (heap : Heap) (left right : Mutable.Value × Mutable.Value) : Bool :=
  negativeLess (readPair heap left.1) (readPair heap right.1)

def sortedRefs (heap : Heap) (entries : List Entry) : List Mutable.Value :=
  (HeapSort.sortBy (less (heap ++ scratch entries)) (cached heap.length entries)).map Prod.fst

def finalHeap (heap : Heap) (entries : List Entry) : Heap :=
  heap ++ scratch entries ++ [.list (sortedRefs heap entries)]

private theorem found_append {heap : Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem read_pair (heap : Heap) (entry : Entry) (found : heap[entry.address]? = some (row entry)) :
    readPair heap (original entry) = entry.pair := by
  simp [readPair, original, TupleSorting.readInts, row, found, Entry.pair]

private theorem cached_fst (start : Nat) (entries : List Entry) :
    (cached start entries).map Prod.fst = items entries := by
  induction entries generalizing start with
  | nil => rfl
  | cons entry rest ih => simp [cached, items, ih]

private theorem cached_append (start : Nat) (entries : List Entry) (entry : Entry) :
    cached start (entries ++ [entry]) = cached start entries ++ [(original entry, .ref (start+entries.length))] := by
  induction entries generalizing start with
  | nil => simp [cached]
  | cons first rest ih => simp [cached, ih, Nat.add_comm, Nat.add_left_comm]

private theorem cached_rows (heap : Heap) (entries : List Entry) :
    List.Forall₂ (fun cache entry => cache.1 = original entry ∧ ∃ address,
      cache.2 = .ref address ∧ (heap ++ scratch entries)[address]? = some (keyRow entry))
      (cached heap.length entries) entries := by
  induction entries generalizing heap with
  | nil => exact .nil
  | cons entry rest ih =>
      apply List.Forall₂.cons
      · exact ⟨rfl, heap.length, rfl, by simp [scratch]⟩
      · simpa [cached, scratch, List.append_assoc] using ih (heap ++ [keyRow entry])

private theorem related_member {α β : Type} (relation : α → β → Prop)
    {left : List α} {right : List β} (related : List.Forall₂ relation left right)
    (item : α) (member : item ∈ left) : ∃ value ∈ right, relation item value := by
  induction related with
  | nil => cases member
  | @cons first value rest values related _ ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨value, List.mem_cons_self, related⟩
      · obtain ⟨foundValue, present, shape⟩ := ih member
        exact ⟨foundValue, List.mem_cons_of_mem _ present, shape⟩

private theorem cached_member (heap : Heap) (entries : List Entry) (cache : Mutable.Value × Mutable.Value)
    (member : cache ∈ cached heap.length entries) :
    ∃ entry ∈ entries, cache.1 = original entry ∧ ∃ address, cache.2 = .ref address ∧
      (heap ++ scratch entries)[address]? = some (keyRow entry) :=
  related_member _ (cached_rows heap entries) cache member

private theorem negative_le (left right : Int × Int) :
    PokerGroupOrder.pairLE (negative left) (negative right) ↔ PokerGroupOrder.pairLE right left := by
  unfold PokerGroupOrder.pairLE negative
  omega

private theorem negative_ordered (pairs : List (Int × Int)) :
    (HeapSort.sortBy negativeLess pairs).Pairwise (fun left right => PokerGroupOrder.pairLE right left) := by
  have mapped := HeapSort.sortBy_map negative PokerGroupOrder.pairLess pairs
  change (HeapSort.sortBy negativeLess pairs).map negative =
    HeapSort.sortBy PokerGroupOrder.pairLess (pairs.map negative) at mapped
  have ordered := PokerGroupOrder.sortBy_ordered (pairs.map negative)
  rw [← mapped] at ordered
  exact (List.pairwise_map.mp ordered).imp (fun {left right} related => (negative_le left right).mp related)

/-- The reference's ascending negated keys decode to descending count/rank pairs. -/
theorem negative_sort_eq (pairs : List (Int × Int)) :
    HeapSort.sortBy negativeLess pairs = PokerGroupOrder.sortedPairs true pairs := by
  apply List.Perm.eq_of_pairwise (le := fun left right => PokerGroupOrder.pairLE right left)
    (fun left right _ _ before after => ?_) (negative_ordered pairs)
    (PokerGroupOrder.sortedPairs_descending pairs)
    ((HeapSort.sortBy_perm negativeLess pairs).trans (PokerGroupOrder.sortedPairs_perm true pairs).symm)
  apply Prod.ext <;> unfold PokerGroupOrder.pairLE at before after <;> omega

private theorem keyed_insert_of_compare (heap : Heap) (compareLess :
    (Mutable.Value × Mutable.Value) → (Mutable.Value × Mutable.Value) → Bool)
    (value : Mutable.Value × Mutable.Value) (keys : List (Mutable.Value × Mutable.Value))
    (compared : ∀ key ∈ keys, HeapSort.compare (heap.length+1) heap false key.2 value.2 =
      some (.ok (compareLess key value))) :
    HeapSort.keyedInsert heap value keys = some (.ok (HeapSort.insertBy compareLess value keys)) := by
  induction keys with
  | nil => rfl
  | cons first rest ih =>
      have firstCompared := compared first List.mem_cons_self
      have restCompared := ih (fun key member => compared key (List.mem_cons_of_mem _ member))
      simp only [HeapSort.keyedInsert, firstCompared, HeapSort.insertBy]
      cases compareLess first value <;> simp [restCompared, Except.map]

private theorem keyed_sort_of_compare (heap : Heap) (compareLess :
    (Mutable.Value × Mutable.Value) → (Mutable.Value × Mutable.Value) → Bool)
    (keys : List (Mutable.Value × Mutable.Value))
    (compared : ∀ left ∈ keys, ∀ right ∈ keys,
      HeapSort.compare (heap.length+1) heap false left.2 right.2 = some (.ok (compareLess left right))) :
    HeapSort.keyedSort heap keys = some (.ok (HeapSort.sortBy compareLess keys)) := by
  induction keys with
  | nil => rfl
  | cons first rest ih =>
      have ordered := ih (fun left hl right hr => compared left (List.mem_cons_of_mem _ hl)
        right (List.mem_cons_of_mem _ hr))
      simp only [HeapSort.keyedSort, ordered, HeapSort.sortBy]
      apply keyed_insert_of_compare
      intro key member
      exact compared key (List.mem_cons_of_mem _ ((HeapSort.sortBy_perm compareLess rest).mem_iff.mp member))
        first List.mem_cons_self

private theorem keys_compared (heap : Heap) (entries : List Entry) (known : Found heap entries)
    (left : Mutable.Value × Mutable.Value) (leftMember : left ∈ cached heap.length entries)
    (right : Mutable.Value × Mutable.Value) (rightMember : right ∈ cached heap.length entries) :
    HeapSort.compare ((heap ++ scratch entries).length+1) (heap ++ scratch entries) false left.2 right.2 =
      some (.ok (less (heap ++ scratch entries) left right)) := by
  obtain ⟨a, aMember, aOriginal, aKey, aReference, aFound⟩ := cached_member heap entries left leftMember
  obtain ⟨b, bMember, bOriginal, bKey, bReference, bFound⟩ := cached_member heap entries right rightMember
  have aRead := read_pair (heap ++ scratch entries) a (found_append (known a aMember) _)
  have bRead := read_pair (heap ++ scratch entries) b (found_append (known b bMember) _)
  have positive : 0 < (heap ++ scratch entries).length := by
    have inside := (List.getElem?_eq_some_iff.mp aFound).1
    omega
  have depth : (heap ++ scratch entries).length-1+2 = (heap ++ scratch entries).length+1 := by omega
  have compared := HeapSort.compare_int_tuples (heap ++ scratch entries) aKey bKey
    ((heap ++ scratch entries).length-1) [-a.count, -a.rank] [-b.count, -b.rank] aFound bFound
  simpa only [depth, aReference, bReference, less, aOriginal, bOriginal, aRead, bRead,
    negativeLess, negative, Entry.pair, PokerGroupOrder.pairLess, PokerGroupOrder.row] using compared

private theorem finish (heap : Heap) (entries : List Entry) (known : Found heap entries) :
    sortedFinish false (cached heap.length entries).reverse (heap ++ scratch entries) =
      some (.ok (.ref (heap ++ scratch entries).length), finalHeap heap entries) := by
  have sorted := keyed_sort_of_compare (heap ++ scratch entries) (less (heap ++ scratch entries))
    (cached heap.length entries) (keys_compared heap entries known)
  simp [sortedFinish, HeapSort.keyedSortWithReverse, sorted, finalHeap, sortedRefs, Mutable.allocate, Except.map]

/-- Sorting retains every input tuple reference, including references with equal numerical contents. -/
theorem sortedRefs_perm (heap : Heap) (entries : List Entry) :
    (sortedRefs heap entries).Perm (items entries) := by
  rw [← cached_fst heap.length entries]
  exact (HeapSort.sortBy_perm (less (heap ++ scratch entries)) (cached heap.length entries)).map Prod.fst

/-- Numerical projection of the actual returned references equals the root's descending group order. -/
theorem sortedRefs_pairs (heap : Heap) (entries : List Entry) (known : Found heap entries) :
    (sortedRefs heap entries).map (readPair (heap ++ scratch entries)) =
      PokerGroupOrder.sortedPairs true (entries.map Entry.pair) := by
  have decoded : (cached heap.length entries).map (fun cache => readPair (heap ++ scratch entries) cache.1) =
      entries.map Entry.pair := by
    change (cached heap.length entries).map (readPair (heap ++ scratch entries) ∘ Prod.fst) = _
    rw [← List.map_map, cached_fst]
    simp only [items, List.map_map]
    apply List.map_congr_left
    intro entry member
    exact read_pair (heap ++ scratch entries) entry (found_append (known entry member) _)
  have mapped := HeapSort.sortBy_map (fun cache : Mutable.Value × Mutable.Value =>
      readPair (heap ++ scratch entries) cache.1) negativeLess (cached heap.length entries)
  change (HeapSort.sortBy (less (heap ++ scratch entries)) (cached heap.length entries)).map
      (fun cache => readPair (heap ++ scratch entries) cache.1) = _ at mapped
  rw [decoded, negative_sort_eq] at mapped
  simpa only [sortedRefs, List.map_map, Function.comp_def] using mapped

private abbrev component (index : Int) : Expr := .subscript (.name "p") (.constant (.int index))
private abbrev keyExpression : Expr := .tuple [.unaryOp .uSub (component 0), .unaryOp .uSub (component 1)]

private theorem key_eval (heap : Heap) (env : HeapCalls.Env) (entry : Entry) (globals : Mutable.Globals)
    (bound : env "p" = some (original entry)) (found : heap[entry.address]? = some (row entry)) :
    Evaluates program env keyExpression heap (.ref heap.length) (heap ++ [keyRow entry]) globals := by
  have first : Evaluates program env (component 0) heap (number entry.count) heap globals := by
    apply Evaluates.subscript (by intros; simp) (Evaluates.lookup bound) Evaluates.constant
    simp [original, Mutable.getItem, Mutable.index, row, found, number, Except.map]
  have second : Evaluates program env (component 1) heap (number entry.rank) heap globals := by
    apply Evaluates.subscript (by intros; simp) (Evaluates.lookup bound) Evaluates.constant
    simp [original, Mutable.getItem, Mutable.index, row, found, number, Except.map]
  exact Evaluates.tuple (.cons (Evaluates.unary first rfl) (.cons (Evaluates.unary second rfl) .nil)) (by simp)

private theorem keys_result (heap : Heap) (env : HeapCalls.Env) (done remaining : List Entry)
    (globals : Mutable.Globals) (known : Found heap (done ++ remaining)) :
    SortedReturns program ⟨"p", keyExpression, env, false⟩ (items remaining)
      (cached heap.length done).reverse (heap ++ scratch done) (.ref (heap ++ scratch (done ++ remaining)).length)
      (finalHeap heap (done ++ remaining)) globals := by
  induction remaining generalizing done with
  | nil =>
      simpa only [List.append_nil] using SortedReturns.done (finish heap done (by simpa using known))
  | cons entry rest ih =>
      have found := found_append (known entry (List.mem_append_right _ List.mem_cons_self)) (scratch done)
      have evaluated := key_eval (heap ++ scratch done) (setLocal env "p" (original entry)) entry globals
        (by simp [setLocal]) found
      have tailKnown : Found heap ((done ++ [entry]) ++ rest) := by
        simpa only [List.append_assoc, List.singleton_append] using known
      have continued := ih (done ++ [entry]) tailKnown
      apply SortedReturns.next evaluated
      simpa [items, scratch, cached_append, List.reverse_append, List.append_assoc] using continued

private abbrev params := ((findFunctionIn program.body "sort_counts").getD ([], [])).1
private abbrev body := ((findFunctionIn program.body "sort_counts").getD ([], [])).2
private abbrev initial (globals : Mutable.Globals) (address : Nat) : HeapCalls.Env :=
  functionEnv params body [.ref address] globals
private theorem get_cs (globals : Mutable.Globals) (address : Nat) : initial globals address "cs" = some (.ref address) := by
  cases globals <;> rfl

/-- The original source lambda allocates one negated key tuple per input item, then a fresh result list. -/
theorem result (heap : Heap) (address : Nat) (entries : List Entry) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (items entries))) (known : Found heap entries) :
    ReturnsValue program "sort_counts" [.ref address] heap (.ref (heap ++ scratch entries).length)
      (finalHeap heap entries) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sorted_sequence (Evaluates.lookup (get_cs globals address)) Evaluates.constant
    (items := items entries) (direction := false) (middle := heap)
  · simp [sortedStart, sortedItems, Mutable.sequence, found, Mutable.truth, scalarTruth]
  · simpa only [List.nil_append, cached, List.reverse_nil, scratch, List.map_nil, List.append_nil] using
      keys_result heap (initial globals address) [] entries globals (by simpa using known)

/-- The caller's original objects remain unchanged throughout both callback collection and sorting. -/
theorem caller_found (heap : Heap) (entries : List Entry) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) : (finalHeap heap entries)[address]? = some object := by
  exact found_append (found_append found (scratch entries)) [.list (sortedRefs heap entries)]

/-- The newly allocated result list contains the sorted original references. -/
theorem returned_found (heap : Heap) (entries : List Entry) :
    (finalHeap heap entries)[(heap ++ scratch entries).length]? = some (.list (sortedRefs heap entries)) := by
  simp [finalHeap]

/-- Reading the source result in its final heap yields the exact descending frequency/rank rows. -/
theorem sortedRefs_rows (heap : Heap) (entries : List Entry) (known : Found heap entries) :
    (sortedRefs heap entries).map (TupleSorting.readInts (finalHeap heap entries)) =
      (PokerGroupOrder.sortedPairs true (entries.map Entry.pair)).map PokerGroupOrder.row := by
  rw [← sortedRefs_pairs heap entries known]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro item member
  obtain ⟨entry, present, rfl⟩ := List.mem_map.mp ((sortedRefs_perm heap entries).mem_iff.mp member)
  have before := found_append (known entry present) (scratch entries)
  have after := caller_found heap entries entry.address (row entry) (known entry present)
  simp [original, TupleSorting.readInts, row, before, after, readPair, PokerGroupOrder.row]

end data.«project-euler-statements».data.py.project_euler_statements.p54.sort_counts_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.counts_key_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

private abbrev program := P54Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev numbers (values : List Int) : List Mutable.Value := values.map number
private abbrev working := HeapCollection.working
private abbrev Entry := sort_counts_source.Entry

def segment (pair : Int × Int) : List Int := List.replicate pair.1.toNat pair.2
def expanded (pairs : List (Int × Int)) : List Int := pairs.flatMap segment
def temporary (pair : Int × Int) : Heap := [.list [number pair.2], .list (numbers (segment pair))]
def temporaries (pairs : List (Int × Int)) : Heap := pairs.flatMap temporary

def countEntries (values : List Int) (start : Nat) : List Int → List Entry
  | [] => []
  | rank :: rest => ⟨start, values.count rank, rank⟩ :: countEntries values (start+1) rest

def countedRows (values : List Int) : List (Int × Int) :=
  (PokerUnique.unique values).map fun rank => ((values.count rank : Int), rank)
def orderedRows (values : List Int) : List (Int × Int) := PokerGroupOrder.sortedPairs true (countedRows values)

def seed (heap : Heap) : Heap := heap ++ [.list []]
def entries (heap : Heap) (values : List Int) : List Entry :=
  countEntries values ((seed heap).length+2) (PokerUnique.unique values)
def countGarbage (heap : Heap) (values : List Int) : Heap :=
  [.list (numbers (PokerUnique.unique values)),
   .list (counts_source.references ((seed heap).length+2) (PokerUnique.unique values))] ++
    counts_source.scratch values (PokerUnique.unique values)
def countedHeap (heap : Heap) (values : List Int) : Heap := seed heap ++ countGarbage heap values

def preparedHeap (heap : Heap) (values : List Int) : Heap :=
  sort_counts_source.finalHeap (countedHeap heap values) (entries heap values)
def sourceAddress (heap : Heap) (values : List Int) : Nat :=
  (countedHeap heap values ++ sort_counts_source.scratch (entries heap values)).length

def baseGarbage (heap : Heap) (values : List Int) : Heap :=
  countGarbage heap values ++ sort_counts_source.scratch (entries heap values) ++
    [.list (sort_counts_source.sortedRefs (countedHeap heap values) (entries heap values))]
def finalHeap (heap : Heap) (values : List Int) : Heap :=
  working heap (numbers (expanded (orderedRows values)))
    (baseGarbage heap values ++ temporaries (orderedRows values))

private theorem found_append {heap : Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Heap) :
    (heap ++ extra)[address]? = some object := HeapCollection.prefix_found heap extra address object found

private theorem items_countEntries (values : List Int) (start : Nat) (keys : List Int) :
    sort_counts_source.items (countEntries values start keys) = counts_source.references start keys := by
  induction keys generalizing start with
  | nil => rfl
  | cons rank rest ih =>
      change (.ref start :: sort_counts_source.items (countEntries values (start+1) rest)) =
        (.ref start :: counts_source.references (start+1) rest)
      exact congrArg (List.cons (.ref start)) (ih (start+1))

private theorem pairs_countEntries (values : List Int) (start : Nat) (keys : List Int) :
    (countEntries values start keys).map sort_counts_source.Entry.pair = keys.map fun rank => ((values.count rank : Int), rank) := by
  induction keys generalizing start with
  | nil => rfl
  | cons rank rest ih => simp [countEntries, sort_counts_source.Entry.pair, ih]

private theorem countEntries_found (values : List Int) (heap : Heap) (keys : List Int) :
    sort_counts_source.Found (heap ++ counts_source.scratch values keys)
      (countEntries values heap.length keys) := by
  induction keys generalizing heap with
  | nil => intro entry impossible; cases impossible
  | cons rank rest ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · simp [counts_source.scratch, counts_source.row, sort_counts_source.row]
      · have found := ih (heap ++ [counts_source.row values rank])
        have remaining : entry ∈ countEntries values (heap ++ [counts_source.row values rank]).length rest := by
          simpa only [List.length_append, List.length_singleton] using member
        simpa [counts_source.scratch, List.append_assoc] using found entry remaining

private theorem counted_known (heap : Heap) (values : List Int) :
    sort_counts_source.Found (countedHeap heap values) (entries heap values) := by
  have found := countEntries_found values
    (seed heap ++ [.list (numbers (PokerUnique.unique values)),
      .list (counts_source.references ((seed heap).length+2) (PokerUnique.unique values))])
    (PokerUnique.unique values)
  simpa [countedHeap, countGarbage, entries, List.append_assoc] using found

private theorem prepared_shape (heap : Heap) (values : List Int) :
    preparedHeap heap values = working heap [] (baseGarbage heap values) := by
  simp [preparedHeap, sort_counts_source.finalHeap, countedHeap, seed, HeapCollection.working, baseGarbage, List.append_assoc]

private theorem source_found (heap : Heap) (values : List Int) :
    (preparedHeap heap values)[sourceAddress heap values]? =
      some (.list (sort_counts_source.sortedRefs (countedHeap heap values) (entries heap values))) :=
  sort_counts_source.returned_found (countedHeap heap values) (entries heap values)

private theorem decode_items (heap : Heap) (originalEntries : List Entry)
    (known : sort_counts_source.Found heap originalEntries) (groups : List Mutable.Value)
    (members : ∀ group ∈ groups, group ∈ sort_counts_source.items originalEntries) :
    ∃ chosen : List Entry, sort_counts_source.items chosen = groups ∧ sort_counts_source.Found heap chosen := by
  induction groups with
  | nil => exact ⟨[], rfl, by intro entry impossible; cases impossible⟩
  | cons group rest ih =>
      obtain ⟨entry, present, equal⟩ := List.mem_map.mp (members group List.mem_cons_self)
      obtain ⟨chosen, shape, found⟩ := ih (fun value member => members value (List.mem_cons_of_mem _ member))
      refine ⟨entry :: chosen, ?_, ?_⟩
      · change sort_counts_source.original entry :: sort_counts_source.items chosen = group :: rest
        rw [equal, shape]
      · intro item member
        rcases List.mem_cons.mp member with same | member
        · subst item
          exact known entry present
        · exact found item member

private theorem rows_of_found (heap : Heap) (chosen : List Entry) (known : sort_counts_source.Found heap chosen) :
    (sort_counts_source.items chosen).map (TupleSorting.readInts heap) =
      (chosen.map sort_counts_source.Entry.pair).map PokerGroupOrder.row := by
  simp only [sort_counts_source.items, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro entry present
  simp [sort_counts_source.original, TupleSorting.readInts, known entry present,
    sort_counts_source.row, PokerGroupOrder.row, sort_counts_source.Entry.pair]

private theorem row_injective : Function.Injective PokerGroupOrder.row := by
  intro left right equal
  have first := congrArg (fun row : List Int => row.getD 0 0) equal
  have second := congrArg (fun row : List Int => row.getD 1 0) equal
  exact Prod.ext (by simpa [PokerGroupOrder.row] using first) (by simpa [PokerGroupOrder.row] using second)

/-- Choose descriptions of the sorted original tuple references without assuming their addresses are distinct. -/
private theorem prepared_entries (heap : Heap) (values : List Int) :
    ∃ chosen : List Entry,
      sort_counts_source.items chosen = sort_counts_source.sortedRefs (countedHeap heap values) (entries heap values) ∧
      sort_counts_source.Found (preparedHeap heap values) chosen ∧
      chosen.map sort_counts_source.Entry.pair = orderedRows values := by
  have originalKnown : sort_counts_source.Found (preparedHeap heap values) (entries heap values) := by
    intro entry member
    exact sort_counts_source.caller_found (countedHeap heap values) (entries heap values)
      entry.address _ (counted_known heap values entry member)
  obtain ⟨chosen, shape, known⟩ := decode_items (preparedHeap heap values) (entries heap values) originalKnown
    (sort_counts_source.sortedRefs (countedHeap heap values) (entries heap values))
    (fun group member => (sort_counts_source.sortedRefs_perm (countedHeap heap values) (entries heap values)).mem_iff.mp member)
  refine ⟨chosen, shape, known, ?_⟩
  have rows := sort_counts_source.sortedRefs_rows (countedHeap heap values) (entries heap values) (counted_known heap values)
  rw [← shape] at rows
  change (sort_counts_source.items chosen).map (TupleSorting.readInts (preparedHeap heap values)) = _ at rows
  rw [rows_of_found _ chosen known] at rows
  have mapped := (List.map_inj_right (f := PokerGroupOrder.row)
    (fun _ _ same => row_injective same)).mp rows
  simpa [entries, pairs_countEntries, orderedRows, countedRows] using mapped

private abbrev chunkExpression : Expr := .binOp (.list [.name "value"]) .mult (.name "count")
private abbrev loopBody : List Stmt := [.augAssign (.name "out") .add chunkExpression]

private theorem chunk_eval (heap : Heap) (env : HeapCalls.Env) (count rank : Int) (globals : Mutable.Globals)
    (getCount : env "count" = some (number count)) (getRank : env "value" = some (number rank)) :
    Evaluates program env chunkExpression heap (.ref (heap.length+1)) (heap ++ temporary (count, rank)) globals := by
  let fresh := heap ++ [Mutable.Object.list [number rank]]
  apply Evaluates.binary (av := .ref heap.length) (bv := number count)
    (middle := fresh) (afterRight := fresh)
  · exact Evaluates.list (.cons (Evaluates.lookup getRank) .nil)
  · exact Evaluates.lookup getCount
  · simp [Mutable.binary, show (BinOp.mult == BinOp.mult) = true from rfl,
      Mutable.array, Mutable.allocate, fresh, temporary, segment, numbers,
      List.map_replicate, List.append_assoc, Except.map]

private theorem append_chunk (heap : Heap) (out : List Int) (garbage : Heap) (env : HeapCalls.Env)
    (count rank : Int) (globals : Mutable.Globals)
    (getOut : env "out" = some (.ref heap.length))
    (getCount : env "count" = some (number count)) (getRank : env "value" = some (number rank)) :
    BlockContinues program env loopBody (working heap (numbers out) garbage)
      (setLocal env "out" (.ref heap.length))
      (working heap (numbers (out ++ segment (count, rank))) (garbage ++ temporary (count, rank))) globals := by
  have evaluated := chunk_eval (working heap (numbers out) garbage) env count rank globals getCount getRank
  have outFound := found_append (HeapCollection.found heap (numbers out) garbage) (temporary (count, rank))
  have rightFound :
      (working heap (numbers out) garbage ++ temporary (count, rank))[(working heap (numbers out) garbage).length+1]? =
        some (.list (numbers (segment (count, rank)))) := by simp [temporary]
  have appended := inplace_add_lists (working heap (numbers out) garbage ++ temporary (count, rank))
    heap.length ((working heap (numbers out) garbage).length+1) (numbers out)
    (numbers (segment (count, rank))) outFound rightFound
  apply BlockContinues.augAssign getOut evaluated
  simpa [HeapCollection.append, HeapCollection.store, numbers, List.map_append] using appended

private theorem collect (heap : Heap) (initialGarbage : Heap) (address : Nat) (all remaining : List Entry)
    (sourceFound : (working heap [] initialGarbage)[address]? = some (.list (sort_counts_source.items all)))
    (different : heap.length ≠ address)
    (known : sort_counts_source.Found (working heap [] initialGarbage) all)
    (position : Nat) (suffix : all.drop position = remaining) (out : List Int) (extra : Heap)
    (env : HeapCalls.Env) (globals : Mutable.Globals) (getOut : env "out" = some (.ref heap.length)) :
    ∃ finalEnv, finalEnv "out" = some (.ref heap.length) ∧
      BlockContinues program env [.unpackStepLoop ["count", "value"] (.ref address) position loopBody []]
        (working heap (numbers out) (initialGarbage ++ extra)) finalEnv
        (working heap (numbers (out ++ expanded (remaining.map sort_counts_source.Entry.pair)))
          (initialGarbage ++ extra ++ temporaries (remaining.map sort_counts_source.Entry.pair))) globals := by
  have sequence (collected : List Int) (more : Heap) :
      Mutable.sequence (.ref address) (working heap (numbers collected) (initialGarbage ++ more)) =
        some (.ok (sort_counts_source.items all), working heap (numbers collected) (initialGarbage ++ more)) := by
    have preserved := HeapCollection.other_found heap [] (numbers collected) initialGarbage more address _ different sourceFound
    simp [Mutable.sequence, preserved]
  induction remaining generalizing position out extra env with
  | nil =>
      have missing : all[position]? = none := by simpa [suffix] using (List.head?_drop (l := all) (i := position)).symm
      refine ⟨env, getOut, ?_⟩
      apply BlockContinues.unpack_done (source := .ref address) (sequence out extra)
        (by simp [sort_counts_source.items, List.getElem?_map, missing])
      simpa [expanded, temporaries] using (BlockContinues.nil (module := program) (env := env)
        (heap := working heap (numbers out) (initialGarbage ++ extra)) (globals := globals))
  | cons entry rest ih =>
      have item : all[position]? = some entry := by simpa [suffix] using (List.head?_drop (l := all) (i := position)).symm
      have member : entry ∈ all := List.mem_of_getElem? item
      have pairFound := known entry member
      have pairDifferent : heap.length ≠ entry.address := by
        intro same
        rw [← same, HeapCollection.found] at pairFound
        cases pairFound
      have fields (collected : List Int) (more : Heap) :
          Mutable.sequence (sort_counts_source.original entry) (working heap (numbers collected) (initialGarbage ++ more)) =
            some (.ok [number entry.count, number entry.rank], working heap (numbers collected) (initialGarbage ++ more)) := by
        have preserved := HeapCollection.other_found heap [] (numbers collected) initialGarbage more
          entry.address _ pairDifferent pairFound
        simp [sort_counts_source.original, Mutable.sequence, preserved, sort_counts_source.row]
      let bound := assignNames env ["count", "value"] [number entry.count, number entry.rank]
      have boundOut : bound "out" = some (.ref heap.length) := by simpa [bound, assignNames, setLocal] using getOut
      have countBound : bound "count" = some (number entry.count) := by simp [bound, assignNames, setLocal]
      have rankBound : bound "value" = some (number entry.rank) := by simp [bound, assignNames, setLocal]
      have appended := append_chunk heap out (initialGarbage ++ extra) bound entry.count entry.rank globals boundOut countBound rankBound
      let after := setLocal bound "out" (.ref heap.length)
      obtain ⟨finalEnv, finalOut, continued⟩ := ih (position+1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) (out ++ segment entry.pair)
        (extra ++ temporary entry.pair) after rfl
      refine ⟨finalEnv, finalOut, ?_⟩
      apply BlockContinues.unpack_step (source := .ref address) (value := sort_counts_source.original entry)
        (values := [number entry.count, number entry.rank]) (sequence out extra)
        (by simp [sort_counts_source.items, List.getElem?_map, item]) (fields out extra) rfl
      have joined := appended.append (by
        simpa only [List.append_assoc, sort_counts_source.Entry.pair] using continued)
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, expanded, temporaries,
        List.append_assoc, sort_counts_source.Entry.pair] using joined

private abbrev params := ((findFunctionIn program.body "counts_key").getD ([], [])).1
private abbrev body := ((findFunctionIn program.body "counts_key").getD ([], [])).2
private abbrev initial (globals : Mutable.Globals) (address : Nat) : HeapCalls.Env :=
  functionEnv params body [.ref address] globals
private theorem get_rs (globals : Mutable.Globals) (address : Nat) : initial globals address "rs" = some (.ref address) := by
  cases globals <;> rfl

/-- The original source composes counting, keyed sorting and repeated-value list concatenation. -/
theorem result (heap : Heap) (address : Nat) (values : List Int) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (numbers values))) :
    ReturnsValue program "counts_key" [.ref address] heap (.ref heap.length) (finalHeap heap values) globals := by
  let ready := setLocal (initial globals address) "out" (.ref heap.length)
  have getRs : ready "rs" = some (.ref address) := by simpa [ready, setLocal] using get_rs globals address
  have seedFound := found_append found [.list []]
  have counted := counts_source.result values (seed heap) address globals seedFound
  have countedRun : Evaluates program ready (.call (.name "rank_counts") [.name "rs"])
      (seed heap) (.ref ((seed heap).length+1)) (countedHeap heap values) globals := by
    apply Evaluates.call (.cons (Evaluates.lookup getRs) .nil)
    simpa [countedHeap, countGarbage, List.append_assoc] using counted
  have countList : (countedHeap heap values)[(seed heap).length+1]? =
      some (.list (sort_counts_source.items (entries heap values))) := by
    simp [countedHeap, countGarbage, entries, items_countEntries]
  have sorted := sort_counts_source.result (countedHeap heap values) ((seed heap).length+1)
    (entries heap values) globals countList (counted_known heap values)
  have sortedRun : Evaluates program ready
      (.call (.name "sort_counts") [.call (.name "rank_counts") [.name "rs"]])
      (seed heap) (.ref (sourceAddress heap values)) (preparedHeap heap values) globals :=
    Evaluates.call (.cons countedRun .nil) sorted
  obtain ⟨chosen, chosenItems, chosenKnown, chosenPairs⟩ := prepared_entries heap values
  have listFound : (working heap [] (baseGarbage heap values))[sourceAddress heap values]? =
      some (.list (sort_counts_source.items chosen)) := by
    simpa [prepared_shape, chosenItems] using source_found heap values
  have different : heap.length ≠ sourceAddress heap values := by
    have larger : heap.length < sourceAddress heap values := by
      simp only [sourceAddress, countedHeap, countGarbage, seed, List.length_append, List.length_cons, List.length_nil]
      omega
    exact Nat.ne_of_lt larger
  obtain ⟨finalEnv, getOut, loop⟩ := collect heap (baseGarbage heap values) (sourceAddress heap values)
    chosen chosen listFound different (by simpa [prepared_shape] using chosenKnown)
    0 rfl [] [] ready globals rfl
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (Evaluates.list .nil)
  apply BlockContinues.returns
    (body := [.forIn (.tuple [.name "count", .name "value"])
      (.call (.name "sort_counts") [.call (.name "rank_counts") [.name "rs"]]) loopBody []])
    (following := [.return (.name "out")]) (middleEnv := finalEnv)
  · apply BlockContinues.for_unpack (items := sort_counts_source.items chosen) (value := .ref (sourceAddress heap values))
      (by
        intro expressions equal
        have functions := congrArg (fun expression => match expression with
          | .call function _ => function
          | _ => .constant .none) equal
        have names := congrArg (fun expression => match expression with
          | .name name => name
          | _ => "") functions
        have impossible : False := by simp at names
        exact impossible.elim) rfl sortedRun
      (by simp [Mutable.sequence, source_found, chosenItems])
    simpa [prepared_shape, chosenPairs, finalHeap] using loop
  · exact BlockReturns.return_value (Evaluates.lookup getOut)

/-- The returned repetition key is a fresh integer list with the mathematical expanded group order. -/
theorem returned_found (heap : Heap) (values : List Int) :
    (finalHeap heap values)[heap.length]? = some (.list (numbers (expanded (orderedRows values)))) := by
  simp [finalHeap, working]

/-- Every caller object survives the helper unchanged. -/
theorem caller_found (heap : Heap) (values : List Int) (address : Nat) (object : Mutable.Object)
    (found : heap[address]? = some object) : (finalHeap heap values)[address]? = some object :=
  found_append found _

/-- Occurrence counts supply nonnegative repetition lengths without restricting source integer ranks. -/
theorem counts_nonnegative (values : List Int) : ∀ pair ∈ countedRows values, 0 ≤ pair.1 := by
  intro pair member
  obtain ⟨rank, present, rfl⟩ := List.mem_map.mp member
  exact Int.natCast_nonneg _

end data.«project-euler-statements».data.py.project_euler_statements.p54.counts_key_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

private abbrev program := P54Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev numbers (values : List Int) : List Mutable.Value := values.map number
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev Card := flush_source.Card
private abbrev params := ((findFunctionIn program.body "hand_score").getD ([], [])).1
private abbrev body := ((findFunctionIn program.body "hand_score").getD ([], [])).2
private abbrev code := executableBody body
private abbrev initial (globals : Mutable.Globals) (address : Nat) : HeapCalls.Env :=
  functionEnv params body [.ref address] globals

structure Prepared where
  heap : Heap
  env : HeapCalls.Env
  ranksAddress : Nat
  sortedAddress : Nat
  keysAddress : Nat

structure Context (state : Prepared) (values : List Int) (suits : List String) : Prop where
  getRanks : state.env "rs" = some (.ref state.ranksAddress)
  getSorted : state.env "sorted_rs" = some (.ref state.sortedAddress)
  getKeys : state.env "key_counts" = some (.ref state.keysAddress)
  getFlush : state.env "flush" = some (flag (flush_source.flush suits))
  getStraight : state.env "straight" = some (flag (PokerStraights.referenceStraight (ScalarSort.ints values)))
  ranksFound : state.heap[state.ranksAddress]? = some (.list (numbers values))
  sortedFound : state.heap[state.sortedAddress]? = some (.list (numbers (ScalarSort.ints values)))
  keysFound : state.heap[state.keysAddress]? =
    some (.list (numbers (counts_key_source.expanded (counts_key_source.orderedRows values))))

private theorem found_append {heap : Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem get_hand (globals : Mutable.Globals) (address : Nat) :
    initial globals address "hand" = some (.ref address) := by cases globals <;> rfl

/-- All five preparation calls execute their original bodies, using the live rank_values dictionary. -/
theorem prepare (heap : Heap) (address tableAddress : Nat) (cards : List Card) (valuation : Card → Int)
    (table : List (Constant × Mutable.Value)) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (flush_source.tokens cards)))
    (tableFound : heap[tableAddress]? = some (.dict table))
    (getTable : globals.lookup "rank_values" = some (.ref tableAddress))
    (valued : ∀ card ∈ cards, ScalarDict.lookup table (.string (String.singleton card.rankChar)) =
      some (number (valuation card))) :
    ∃ state : Prepared, ∃ extra : Heap,
      state.heap = heap ++ extra ∧
      BlockContinues program (initial globals address) (code.take 5) heap state.env state.heap globals ∧
      Context state (cards.map valuation) (flush_source.suits cards) := by
  let values := cards.map valuation
  let h1 := heap ++ [.list (numbers values)]
  let e1 := setLocal (initial globals address) "rs" (.ref heap.length)
  have ranked := rank_source.hand_ranks.result cards valuation heap address tableAddress table globals
    found tableFound getTable valued
  have rankedRun : Evaluates program (initial globals address) (.call (.name "hand_ranks") [.name "hand"])
      heap (.ref heap.length) h1 globals := by
    apply Evaluates.call (.cons (Evaluates.lookup (get_hand globals address)) .nil)
    simpa [h1, values, rank_source.ranks, numbers, List.map_map] using ranked
  have ranksFound : h1[heap.length]? = some (.list (numbers values)) := by simp [h1]
  have originalHand : h1[address]? = some (.list (flush_source.tokens cards)) := found_append found _
  obtain ⟨flushExtra, flushed⟩ := flush_source.is_flush.result cards h1 address globals originalHand
  let h2 := h1 ++ flushExtra
  let e2 := setLocal e1 "flush" (flag (flush_source.flush (flush_source.suits cards)))
  have hand1 : e1 "hand" = some (.ref address) := by simpa [e1, setLocal] using get_hand globals address
  have flushedRun : Evaluates program e1 (.call (.name "is_flush") [.name "hand"]) h1
      (flag (flush_source.flush (flush_source.suits cards))) h2 globals :=
    Evaluates.call (.cons (Evaluates.lookup hand1) .nil) flushed
  have ranks2 : h2[heap.length]? = some (.list (numbers values)) := found_append ranksFound _
  let h3 := h2 ++ [.list (numbers (ScalarSort.ints values)), .list (numbers PokerStraights.wheel)]
  let e3 := setLocal e2 "straight" (flag (PokerStraights.referenceStraight (ScalarSort.ints values)))
  have getRanks2 : e2 "rs" = some (.ref heap.length) := by simp [e2, e1, setLocal]
  have straightRun : Evaluates program e2 (.call (.name "is_straight") [.name "rs"]) h2
      (flag (PokerStraights.referenceStraight (ScalarSort.ints values))) h3 globals :=
    Evaluates.call (.cons (Evaluates.lookup getRanks2) .nil) (is_straight.result values h2 heap.length globals ranks2)
  let h4 := h3 ++ [.list (numbers (ScalarSort.ints values))]
  let e4 := setLocal e3 "sorted_rs" (.ref h3.length)
  have ranks3 : h3[heap.length]? = some (.list (numbers values)) := found_append ranks2 _
  have getRanks3 : e3 "rs" = some (.ref heap.length) := by simp [e3, e2, e1, setLocal]
  have sortedRun : Evaluates program e3 (.call (.name "sorted_ranks") [.name "rs"]) h3
      (.ref h3.length) h4 globals :=
    Evaluates.call (.cons (Evaluates.lookup getRanks3) .nil)
      (sorted_ranks.result (globals := globals) values h3 heap.length ranks3)
  let h5 := counts_key_source.finalHeap h4 values
  let e5 := setLocal e4 "key_counts" (.ref h4.length)
  have ranks4 : h4[heap.length]? = some (.list (numbers values)) := found_append ranks3 _
  have getRanks4 : e4 "rs" = some (.ref heap.length) := by simp [e4, e3, e2, e1, setLocal]
  have keyedRun : Evaluates program e4 (.call (.name "counts_key") [.name "rs"]) h4
      (.ref h4.length) h5 globals :=
    Evaluates.call (.cons (Evaluates.lookup getRanks4) .nil) (counts_key_source.result h4 heap.length values globals ranks4)
  have prefixRun : BlockContinues program (initial globals address) (code.take 5) heap e5 h5 globals :=
    (BlockContinues.assign rankedRun).append ((BlockContinues.assign flushedRun).append
      ((BlockContinues.assign straightRun).append ((BlockContinues.assign sortedRun).append
        (BlockContinues.assign keyedRun))))
  let extra := [.list (numbers values)] ++ flushExtra ++
    [.list (numbers (ScalarSort.ints values)), .list (numbers PokerStraights.wheel)] ++
    [.list (numbers (ScalarSort.ints values))] ++
    (.list (numbers (counts_key_source.expanded (counts_key_source.orderedRows values))) ::
      (counts_key_source.baseGarbage h4 values ++ counts_key_source.temporaries (counts_key_source.orderedRows values)))
  refine ⟨⟨h5, e5, heap.length, h3.length, h4.length⟩, extra, ?_, prefixRun, ?_⟩
  · simp [h5, counts_key_source.finalHeap, ProjectEulerSolutions.HeapCollection.working,
      extra, h4, h3, h2, h1, List.append_assoc]
  · constructor
    · simp [e5, e4, e3, e2, e1, setLocal]
    · simp [e5, e4, setLocal]
    · simp [e5, setLocal]
    · simp [e5, e4, e3, e2, setLocal]
    · simp [e5, e4, e3, setLocal, values]
    · exact counts_key_source.caller_found h4 values heap.length _ ranks4
    · have foundSorted : h4[h3.length]? = some (.list (numbers (ScalarSort.ints values))) := by simp [h4]
      exact counts_key_source.caller_found h4 values h3.length _ foundSorted
    · exact counts_key_source.returned_found h4 values

/-- Attach a proved executable category suffix to the actual preparation source. -/
theorem result_of_suffix (heap : Heap) (address : Nat) (state : Prepared) (answer : Mutable.Value)
    (finalHeap : Heap) (globals : Mutable.Globals)
    (prepared : BlockContinues program (initial globals address) (code.take 5) heap state.env state.heap globals)
    (suffix : BlockReturns program state.env (code.drop 5) state.heap answer finalHeap globals) :
    ReturnsValue program "hand_score" [.ref address] heap answer finalHeap globals := by
  apply BlockReturns.function rfl rfl
  simpa only [List.take_append_drop] using prepared.returns suffix

/-- Reference scores contain a category integer and a reference to an ordinary integer LIST. -/
def Represents (heap : Heap) (value : Mutable.Value) (category : Int) (key : List Int) : Prop :=
  ∃ tupleAddress listAddress, value = .ref tupleAddress ∧
    heap[tupleAddress]? = some (.tuple [number category, .ref listAddress]) ∧
    heap[listAddress]? = some (.list (numbers key))

end data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

private abbrev sfProgram := P54Ast.module
private abbrev sfNumber (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev sfNumbers (values : List Int) : List Mutable.Value := values.map sfNumber
private abbrev sfFlag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev sfCode := executableBody ((findFunctionIn sfProgram.body "hand_score").getD ([], [])).2

def royal : List Int := [10, 11, 12, 13, 14]
def straightFlushCategory (values : List Int) : Int := if ScalarSort.ints values = royal then 9 else 8
def straightFlushKey (values : List Int) : List Int :=
  if ScalarSort.ints values = royal then [] else [straight_high.value values]

private abbrev royalExpression : Expr := .list
  [.constant (.int 10), .constant (.int 11), .constant (.int 12), .constant (.int 13), .constant (.int 14)]
private abbrev royalTest : Expr := .compare (.name "sorted_rs") [(.eq, royalExpression)]
private abbrev straightFlushTest : Expr := .boolOp .and [.name "straight", .name "flush"]
private abbrev straightFlushReturn : Expr := .ifExp royalTest
  (.tuple [.constant (.int 9), .list []])
  (.tuple [.constant (.int 8), .list [.call (.name "straight_high") [.name "rs"]]])

private theorem sf_found_append {heap : Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem royal_test (state : Prepared) (values : List Int) (suits : List String)
    (context : Context state values suits) (globals : Mutable.Globals) :
    Evaluates sfProgram state.env royalTest state.heap (sfFlag (decide (ScalarSort.ints values = royal)))
      (state.heap ++ [.list (sfNumbers royal)]) globals := by
  let afterRoyal := state.heap ++ [.list (sfNumbers royal)]
  have different : state.sortedAddress ≠ state.heap.length := by
    have inside := (List.getElem?_eq_some_iff.mp context.sortedFound).1
    omega
  have old : afterRoyal[state.sortedAddress]? = some (.list (sfNumbers (ScalarSort.ints values))) :=
    sf_found_append context.sortedFound _
  have literal : afterRoyal[state.heap.length]? = some (.list (sfNumbers royal)) := by simp [afterRoyal]
  apply Evaluates.compare (av := .ref state.sortedAddress) (bv := .ref state.heap.length)
    (middle := state.heap) (afterRight := afterRoyal) (Evaluates.lookup context.getSorted)
  · exact Evaluates.list (.cons Evaluates.constant (.cons Evaluates.constant
      (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil)))))
  · simp [HeapCalls.compare, Mutable.array, old, literal, different, equalLists_ints, sfNumbers, sfFlag]
    exact ⟨rfl, rfl⟩

private theorem sf_test (state : Prepared) (values : List Int) (suits : List String)
    (context : Context state values suits) (globals : Mutable.Globals)
    (straight : PokerStraights.referenceStraight (ScalarSort.ints values) = true)
    (flush : flush_source.flush suits = true) :
    Evaluates sfProgram state.env straightFlushTest state.heap (sfFlag true) state.heap globals := by
  have getStraight : state.env "straight" = some (sfFlag true) := by simpa [straight] using context.getStraight
  have getFlush : state.env "flush" = some (sfFlag true) := by simpa [flush] using context.getFlush
  exact Evaluates.boolean_next (flag := true) (Evaluates.lookup getStraight) rfl rfl
    (Evaluates.boolean_last (flag := true) (Evaluates.lookup getFlush) rfl)

/-- Royal and ordinary straight flushes execute the source's distinct category-9/category-8 returns. -/
theorem straight_flush_suffix (state : Prepared) (values : List Int) (suits : List String)
    (context : Context state values suits) (globals : Mutable.Globals)
    (straight : PokerStraights.referenceStraight (ScalarSort.ints values) = true)
    (flush : flush_source.flush suits = true) :
    ∃ extra : Heap, ∃ answer : Mutable.Value,
      BlockReturns sfProgram state.env (sfCode.drop 5) state.heap answer (state.heap ++ extra) globals ∧
      Represents (state.heap ++ extra) answer (straightFlushCategory values) (straightFlushKey values) := by
  let afterRoyal := state.heap ++ [.list (sfNumbers royal)]
  have tested := royal_test state values suits context globals
  have straightFlush := sf_test state values suits context globals straight flush
  by_cases isRoyal : ScalarSort.ints values = royal
  · let afterKey := afterRoyal ++ [.list []]
    let finished := afterKey ++ [.tuple [sfNumber 9, .ref afterRoyal.length]]
    have key : Evaluates sfProgram state.env (.list []) afterRoyal (.ref afterRoyal.length) afterKey globals :=
      Evaluates.list .nil
    have tuple : Evaluates sfProgram state.env (.tuple [.constant (.int 9), .list []]) afterRoyal
        (.ref afterKey.length) finished globals :=
      Evaluates.tuple (.cons Evaluates.constant (.cons key .nil)) (by simp)
    have returned : BlockReturns sfProgram state.env (sfCode.drop 5) state.heap (.ref afterKey.length) finished globals := by
      apply BlockReturns.branch (flag := true) straightFlush rfl
      apply BlockReturns.return_value
      exact Evaluates.conditional (flag := true) (value := sfFlag true) (middle := afterRoyal)
        (by simpa [isRoyal] using tested) rfl tuple
    refine ⟨[.list (sfNumbers royal), .list [], .tuple [sfNumber 9, .ref afterRoyal.length]], .ref afterKey.length,
      by simpa [finished, afterKey, afterRoyal, List.append_assoc] using returned, ?_⟩
    refine ⟨afterKey.length, afterRoyal.length, rfl, ?_, ?_⟩
    · simp [straightFlushCategory, isRoyal, afterKey, afterRoyal]
    · simp [straightFlushKey, isRoyal, afterRoyal]
  · let afterHigh := afterRoyal ++ [.list (sfNumbers (ScalarSort.ints values)), .list (sfNumbers straight_high.wheel)]
    let afterKey := afterHigh ++ [.list [sfNumber (straight_high.value values)]]
    let finished := afterKey ++ [.tuple [sfNumber 8, .ref afterHigh.length]]
    have original : afterRoyal[state.ranksAddress]? = some (.list (sfNumbers values)) :=
      sf_found_append context.ranksFound _
    have high : Evaluates sfProgram state.env (.call (.name "straight_high") [.name "rs"])
        afterRoyal (sfNumber (straight_high.value values)) afterHigh globals :=
      Evaluates.call (.cons (Evaluates.lookup context.getRanks) .nil)
        (straight_high.result (globals := globals) values afterRoyal state.ranksAddress original)
    have key : Evaluates sfProgram state.env (.list [.call (.name "straight_high") [.name "rs"]]) afterRoyal
        (.ref afterHigh.length) afterKey globals := Evaluates.list (.cons high .nil)
    have tuple : Evaluates sfProgram state.env
        (.tuple [.constant (.int 8), .list [.call (.name "straight_high") [.name "rs"]]]) afterRoyal
        (.ref afterKey.length) finished globals :=
      Evaluates.tuple (.cons Evaluates.constant (.cons key .nil)) (by simp)
    have returned : BlockReturns sfProgram state.env (sfCode.drop 5) state.heap (.ref afterKey.length) finished globals := by
      apply BlockReturns.branch (flag := true) straightFlush rfl
      apply BlockReturns.return_value
      exact Evaluates.conditional (flag := false) (value := sfFlag false) (middle := afterRoyal)
        (by simpa [isRoyal] using tested) rfl tuple
    refine ⟨[.list (sfNumbers royal), .list (sfNumbers (ScalarSort.ints values)), .list (sfNumbers straight_high.wheel),
      .list [sfNumber (straight_high.value values)], .tuple [sfNumber 8, .ref afterHigh.length]], .ref afterKey.length,
      by simpa [finished, afterKey, afterHigh, afterRoyal, List.append_assoc] using returned, ?_⟩
    refine ⟨afterKey.length, afterHigh.length, rfl, ?_, ?_⟩
    · simp [straightFlushCategory, isRoyal, afterKey, afterHigh, afterRoyal]
    · simp [straightFlushKey, isRoyal, afterHigh, afterRoyal]

/-- This complete hand_score source theorem has no assumed callee executions or fixed rank table. -/
theorem straight_flush_result (heap : Heap) (address tableAddress : Nat) (cards : List flush_source.Card)
    (valuation : flush_source.Card → Int) (table : List (Constant × Mutable.Value)) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (flush_source.tokens cards)))
    (tableFound : heap[tableAddress]? = some (.dict table))
    (getTable : globals.lookup "rank_values" = some (.ref tableAddress))
    (valued : ∀ card ∈ cards, ScalarDict.lookup table (.string (String.singleton card.rankChar)) =
      some (sfNumber (valuation card)))
    (straight : PokerStraights.referenceStraight (ScalarSort.ints (cards.map valuation)) = true)
    (flush : flush_source.flush (flush_source.suits cards) = true) :
    ∃ extra : Heap, ∃ answer : Mutable.Value,
      ReturnsValue sfProgram "hand_score" [.ref address] heap answer (heap ++ extra) globals ∧
      Represents (heap ++ extra) answer (straightFlushCategory (cards.map valuation)) (straightFlushKey (cards.map valuation)) := by
  obtain ⟨state, prefixExtra, shape, prepared, context⟩ := prepare heap address tableAddress cards valuation table globals
    found tableFound getTable valued
  obtain ⟨suffixExtra, answer, suffix, represented⟩ := straight_flush_suffix state (cards.map valuation)
    (flush_source.suits cards) context globals straight flush
  refine ⟨prefixExtra ++ suffixExtra, answer, ?_, ?_⟩
  · simpa only [shape, List.append_assoc] using
      result_of_suffix heap address state answer (state.heap ++ suffixExtra) globals prepared suffix
  · simpa only [shape, List.append_assoc] using represented

end data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.counts_key
open FormalSW.PyAst

theorem «Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call P54Ast.module "counts_key" [.ref address] heap).Returns := by
  obtain ⟨values, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (counts_key_source.result heap address values [] found).returns

theorem «Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call P54Ast.module "counts_key" [.ref address] heap).Supported :=
  («Returns» heap address valid typed).supported

end data.«project-euler-statements».data.py.project_euler_statements.p54.counts_key

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
set_option Elab.async false

private abbrev returnProgram := P54Ast.module
private abbrev returnNumber (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev returnNumbers (values : List Int) : List Mutable.Value := values.map returnNumber

private theorem return_found_append {heap : Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- Repeated-rank categories return their existing key_counts list without copying it. -/
theorem return_existing (heap : Heap) (env : HeapCalls.Env) (category : Int) (keyName : String)
    (keyAddress : Nat) (key : List Int) (rest : List Stmt) (globals : Mutable.Globals)
    (bound : env keyName = some (.ref keyAddress))
    (found : heap[keyAddress]? = some (.list (returnNumbers key))) :
    BlockReturns returnProgram env (.return (.tuple [.constant (.int category), .name keyName]) :: rest)
      heap (.ref heap.length) (heap ++ [.tuple [returnNumber category, .ref keyAddress]]) globals ∧
    Represents (heap ++ [.tuple [returnNumber category, .ref keyAddress]]) (.ref heap.length) category key := by
  constructor
  · apply BlockReturns.return_value
    exact Evaluates.tuple (.cons Evaluates.constant (.cons (Evaluates.lookup bound) .nil)) (by simp)
  · exact ⟨heap.length, keyAddress, rfl, by simp, return_found_append found _⟩

/-- Flush and high-card categories reverse the prepared sorted list into a fresh list key. -/
theorem return_reversed (heap : Heap) (env : HeapCalls.Env) (category : Int) (sortedName : String)
    (sortedAddress : Nat) (values : List Int) (rest : List Stmt) (globals : Mutable.Globals)
    (bound : env sortedName = some (.ref sortedAddress))
    (found : heap[sortedAddress]? = some (.list (returnNumbers values))) :
    BlockReturns returnProgram env
      (.return (.tuple [.constant (.int category), .reversedList (.name sortedName)]) :: rest)
      heap (.ref (heap.length+1))
      (heap ++ [.list (returnNumbers values.reverse), .tuple [returnNumber category, .ref heap.length]]) globals ∧
    Represents (heap ++ [.list (returnNumbers values.reverse), .tuple [returnNumber category, .ref heap.length]])
      (.ref (heap.length+1)) category values.reverse := by
  have reversed := Evaluates.reversed_list (module := returnProgram) (env := env) (globals := globals)
    (Evaluates.lookup bound) found
  have evaluated : Evaluates returnProgram env
      (.tuple [.constant (.int category), .reversedList (.name sortedName)]) heap
      (.ref (heap ++ [Mutable.Object.list ((returnNumbers values).reverse)]).length)
      ((heap ++ [Mutable.Object.list ((returnNumbers values).reverse)]) ++ [.tuple [returnNumber category, .ref heap.length]]) globals :=
    Evaluates.tuple (.cons Evaluates.constant (.cons reversed .nil)) (by simp)
  constructor
  · apply BlockReturns.return_value
    simpa [returnNumbers, List.map_reverse] using evaluated
  · exact ⟨heap.length+1, heap.length, rfl, by simp, by simp⟩

/-- The straight category calls the original straight_high helper before allocating its list key and score tuple. -/
theorem return_straight (heap : Heap) (env : HeapCalls.Env) (ranksAddress : Nat) (values : List Int)
    (rest : List Stmt) (globals : Mutable.Globals) (bound : env "rs" = some (.ref ranksAddress))
    (found : heap[ranksAddress]? = some (.list (returnNumbers values))) :
    ∃ extra : Heap, ∃ answer : Mutable.Value,
      BlockReturns returnProgram env
        (.return (.tuple [.constant (.int 4), .list [.call (.name "straight_high") [.name "rs"]]]) :: rest)
        heap answer (heap ++ extra) globals ∧
      Represents (heap ++ extra) answer 4 [straight_high.value values] := by
  let afterHigh := heap ++ [.list (returnNumbers (ScalarSort.ints values)), .list (returnNumbers straight_high.wheel)]
  let afterKey := afterHigh ++ [.list [returnNumber (straight_high.value values)]]
  let finished := afterKey ++ [.tuple [returnNumber 4, .ref afterHigh.length]]
  have high : Evaluates returnProgram env (.call (.name "straight_high") [.name "rs"]) heap
      (returnNumber (straight_high.value values)) afterHigh globals :=
    Evaluates.call (.cons (Evaluates.lookup bound) .nil)
      (straight_high.result (globals := globals) values heap ranksAddress found)
  have key : Evaluates returnProgram env (.list [.call (.name "straight_high") [.name "rs"]]) heap
      (.ref afterHigh.length) afterKey globals := Evaluates.list (.cons high .nil)
  have tuple : Evaluates returnProgram env
      (.tuple [.constant (.int 4), .list [.call (.name "straight_high") [.name "rs"]]]) heap
      (.ref afterKey.length) finished globals :=
    Evaluates.tuple (.cons Evaluates.constant (.cons key .nil)) (by simp)
  refine ⟨[.list (returnNumbers (ScalarSort.ints values)), .list (returnNumbers straight_high.wheel),
    .list [returnNumber (straight_high.value values)], .tuple [returnNumber 4, .ref afterHigh.length]],
    .ref afterKey.length, ?_, ?_⟩
  · apply BlockReturns.return_value
    simpa [afterHigh, afterKey, finished, List.append_assoc] using tuple
  · refine ⟨afterKey.length, afterHigh.length, rfl, ?_, ?_⟩ <;> simp [afterKey, afterHigh]

end data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
set_option Elab.async false

private abbrev guardProgram := P54Ast.module
private abbrev guardNumber (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev guardFlag (value : Bool) : Mutable.Value := .scalar (.bool value)

def GroupRows (heap : Heap) (groups : List Mutable.Value) (pairs : List (Int × Int)) : Prop :=
  List.Forall₂ (fun value pair => ∃ address, value = .ref address ∧
    heap[address]? = some (.tuple [guardNumber pair.1, guardNumber pair.2])) groups pairs

structure GroupContext (heap : Heap) (env : HeapCalls.Env) (address : Nat)
    (groups : List Mutable.Value) (pairs : List (Int × Int)) : Prop where
  getGroups : env "sc" = some (.ref address)
  groupsFound : heap[address]? = some (.list groups)
  rows : GroupRows heap groups pairs

private theorem group_length (heap : Heap) (groups : List Mutable.Value) (pairs : List (Int × Int))
    (rows : GroupRows heap groups pairs) : groups.length = pairs.length := by
  induction rows with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

private theorem group_at (heap : Heap) (groups : List Mutable.Value) (pairs : List (Int × Int))
    (rows : GroupRows heap groups pairs) (index : Nat) (pair : Int × Int)
    (element : pairs[index]? = some pair) :
    ∃ address, groups[index]? = some (.ref address) ∧
      heap[address]? = some (.tuple [guardNumber pair.1, guardNumber pair.2]) := by
  induction rows generalizing index with
  | nil => simp at element
  | @cons value first groups pairs related _ ih =>
      cases index with
      | zero =>
          have same : first = pair := by simpa using element
          subst pair
          obtain ⟨address, rfl, found⟩ := related
          exact ⟨address, rfl, found⟩
      | succ index =>
          obtain ⟨address, selected, found⟩ := ih index element
          exact ⟨address, selected, found⟩

private abbrev groupField (index field : Int) : Expr :=
  .subscript (.subscript (.name "sc") (.constant (.int index))) (.constant (.int field))
private abbrev countComparison (index : Nat) (count : Int) : Expr :=
  .compare (groupField index 0) [(.eq, .constant (.int count))]
private abbrev nonemptyCountTest (count : Int) : Expr := .boolOp .and [.name "sc", countComparison 0 count]
private abbrev lengthTwoTest : Expr := .compare (.builtinCall .len [.name "sc"]) [(.gtE, .constant (.int 2))]
private abbrev twoCountTest (first second : Int) : Expr :=
  .boolOp .and [lengthTwoTest, countComparison 0 first, countComparison 1 second]

def firstCount (pairs : List (Int × Int)) : Int := ((pairs[0]?).map Prod.fst).getD 0
def secondCount (pairs : List (Int × Int)) : Int := ((pairs[1]?).map Prod.fst).getD 0

private theorem read_count (heap : Heap) (env : HeapCalls.Env) (address : Nat)
    (groups : List Mutable.Value) (pairs : List (Int × Int)) (index : Nat) (pair : Int × Int)
    (context : GroupContext heap env address groups pairs) (globals : Mutable.Globals)
    (element : pairs[index]? = some pair) :
    Evaluates guardProgram env (groupField index 0) heap (guardNumber pair.1) heap globals := by
  obtain ⟨tupleAddress, selected, found⟩ := group_at heap groups pairs context.rows index pair element
  have inside := (List.getElem?_eq_some_iff.mp selected).1
  have getItem := Mutable.getItem_list heap address index groups context.groupsFound inside
  have outer : Evaluates guardProgram env (.subscript (.name "sc") (.constant (.int index))) heap
      (.ref tupleAddress) heap globals := by
    apply Evaluates.subscript (by intros; simp) (Evaluates.lookup context.getGroups) Evaluates.constant
    simpa only [(List.getElem?_eq_some_iff.mp selected).2] using getItem
  apply Evaluates.subscript (by intros; simp) outer Evaluates.constant
  simp [Mutable.getItem, Mutable.index, found, guardNumber, Except.map]

private theorem compared_count (heap : Heap) (env : HeapCalls.Env) (address : Nat)
    (groups : List Mutable.Value) (pairs : List (Int × Int)) (index : Nat) (pair : Int × Int) (count : Int)
    (context : GroupContext heap env address groups pairs) (globals : Mutable.Globals)
    (element : pairs[index]? = some pair) :
    Evaluates guardProgram env (countComparison index count) heap (guardFlag (decide (pair.1 = count))) heap globals := by
  apply Evaluates.compare (read_count heap env address groups pairs index pair context globals element) Evaluates.constant
  rfl

/-- Empty sc short-circuits before sc[0]; nonempty sc compares the first source tuple count. -/
theorem nonempty_count_test (heap : Heap) (env : HeapCalls.Env) (address : Nat)
    (groups : List Mutable.Value) (pairs : List (Int × Int)) (count : Int)
    (context : GroupContext heap env address groups pairs) (globals : Mutable.Globals) :
    ∃ value, Evaluates guardProgram env (nonemptyCountTest count) heap value heap globals ∧
      Mutable.truth value heap = some (.ok (!pairs.isEmpty && decide (firstCount pairs = count)), heap) := by
  cases pairs with
  | nil =>
      have empty : groups = [] := List.eq_nil_of_length_eq_zero (group_length heap groups [] context.rows)
      subst groups
      refine ⟨.ref address, ?_, ?_⟩
      · exact Evaluates.boolean_stop (flag := false) (Evaluates.lookup context.getGroups)
          (by simp [Mutable.truth, context.groupsFound]) rfl
      · simp [Mutable.truth, context.groupsFound]
  | cons pair rest =>
      have nonempty : groups ≠ [] := by
        intro empty
        have length := group_length heap groups (pair :: rest) context.rows
        simp [empty] at length
      have truth : Mutable.truth (.ref address) heap = some (.ok true, heap) := by
        simp [Mutable.truth, context.groupsFound, nonempty]
      refine ⟨guardFlag (decide (pair.1 = count)), ?_, ?_⟩
      · exact Evaluates.boolean_next (flag := true) (Evaluates.lookup context.getGroups) truth rfl
          (Evaluates.boolean_last (flag := decide (pair.1 = count))
            (compared_count heap env address groups (pair :: rest) 0 pair count context globals rfl) rfl)
      · simp [firstCount, Mutable.truth, scalarTruth]

private theorem length_two (heap : Heap) (env : HeapCalls.Env) (address : Nat)
    (groups : List Mutable.Value) (pairs : List (Int × Int))
    (context : GroupContext heap env address groups pairs) (globals : Mutable.Globals) :
    Evaluates guardProgram env lengthTwoTest heap (guardFlag (decide (2 ≤ pairs.length))) heap globals := by
  have size : Evaluates guardProgram env (.builtinCall .len [.name "sc"]) heap
      (guardNumber pairs.length) heap globals := by
    apply Evaluates.builtin (.cons (Evaluates.lookup context.getGroups) .nil)
    simp [primitive, Mutable.length, context.groupsFound, group_length heap groups pairs context.rows]
  apply Evaluates.compare (op := .gtE) size Evaluates.constant
  simp [HeapCalls.compare, scalarCompare, evalCmpOp, guardFlag]
  omega

/-- The length guard protects both indexed count reads in full-house and two-pair tests. -/
theorem two_count_test (heap : Heap) (env : HeapCalls.Env) (address : Nat)
    (groups : List Mutable.Value) (pairs : List (Int × Int)) (first second : Int)
    (context : GroupContext heap env address groups pairs) (globals : Mutable.Globals) :
    Evaluates guardProgram env (twoCountTest first second) heap
      (guardFlag (decide (2 ≤ pairs.length) && decide (firstCount pairs = first) &&
        decide (secondCount pairs = second))) heap globals := by
  have length := length_two heap env address groups pairs context globals
  cases pairs with
  | nil =>
      exact Evaluates.boolean_stop (flag := false) (by simpa using length) rfl rfl
  | cons left rest =>
      cases rest with
      | nil =>
          exact Evaluates.boolean_stop (flag := false) (by simpa using length) rfl rfl
      | cons right rest =>
          have leftTest := compared_count heap env address groups (left :: right :: rest) 0 left first context globals rfl
          have rightTest := compared_count heap env address groups (left :: right :: rest) 1 right second context globals rfl
          apply Evaluates.boolean_next (flag := true) (by simpa using length) rfl rfl
          cases accepted : decide (left.1 = first) with
          | false =>
              simpa [firstCount, secondCount, accepted] using
                (Evaluates.boolean_stop (op := .and) (rest := [countComparison 1 second]) (flag := false)
                  (by simpa [accepted] using leftTest) rfl rfl)
          | true =>
              simpa [firstCount, secondCount, accepted] using
                (Evaluates.boolean_next (op := .and) (flag := true) (by simpa [accepted] using leftTest) rfl rfl
                  (Evaluates.boolean_last (flag := decide (right.1 = second)) rightTest rfl))

end data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

private abbrev groupProgram := P54Ast.module
private abbrev groupNumber (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev groupNumbers (values : List Int) : List Mutable.Value := values.map groupNumber
private abbrev groupEntry := sort_counts_source.Entry
private abbrev groupExpression : Expr :=
  .call (.name "sort_counts") [.call (.name "rank_counts") [.name "rs"]]

private theorem groups_found_append {heap : Heap} {address : Nat} {object : Mutable.Object}
    (found : heap[address]? = some object) (extra : Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem entry_items (values : List Int) (start : Nat) (keys : List Int) :
    sort_counts_source.items (counts_key_source.countEntries values start keys) = counts_source.references start keys := by
  induction keys generalizing start with
  | nil => rfl
  | cons rank rest ih =>
      change (.ref start :: sort_counts_source.items (counts_key_source.countEntries values (start+1) rest)) =
        (.ref start :: counts_source.references (start+1) rest)
      exact congrArg (List.cons (.ref start)) (ih (start+1))

private theorem entry_pairs (values : List Int) (start : Nat) (keys : List Int) :
    (counts_key_source.countEntries values start keys).map sort_counts_source.Entry.pair =
      keys.map fun rank => ((values.count rank : Int), rank) := by
  induction keys generalizing start with
  | nil => rfl
  | cons rank rest ih => simp [counts_key_source.countEntries, sort_counts_source.Entry.pair, ih]

private theorem entry_known (values : List Int) (heap : Heap) (keys : List Int) :
    sort_counts_source.Found (heap ++ counts_source.scratch values keys)
      (counts_key_source.countEntries values heap.length keys) := by
  induction keys generalizing heap with
  | nil => intro entry impossible; cases impossible
  | cons rank rest ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · simp [counts_source.scratch, counts_source.row, sort_counts_source.row]
      · have found := ih (heap ++ [counts_source.row values rank])
        have remaining : entry ∈ counts_key_source.countEntries values (heap ++ [counts_source.row values rank]).length rest := by
          simpa only [List.length_append, List.length_singleton] using member
        simpa [counts_source.scratch, List.append_assoc] using found entry remaining

private theorem rows_of_typed (heap : Heap) (groups : List Mutable.Value) (pairs : List (Int × Int))
    (typed : ∀ value ∈ groups, ∃ (address : Nat) (pair : Int × Int), value = .ref address ∧
      heap[address]? = some (.tuple [groupNumber pair.1, groupNumber pair.2]))
    (decoded : groups.map (TupleSorting.readInts heap) = pairs.map PokerGroupOrder.row) : GroupRows heap groups pairs := by
  induction groups generalizing pairs with
  | nil =>
      have empty : pairs = [] := List.map_eq_nil_iff.mp decoded.symm
      subst pairs
      exact .nil
  | cons value rest ih =>
      cases pairs with
      | nil => simp at decoded
      | cons pair pairs =>
          simp only [List.map_cons, List.cons.injEq] at decoded
          obtain ⟨address, actual, rfl, found⟩ := typed value List.mem_cons_self
          have rowsEqual : PokerGroupOrder.row actual = PokerGroupOrder.row pair := by
            simpa [TupleSorting.readInts, found, PokerGroupOrder.row] using decoded.1
          have first := congrArg (fun row : List Int => row.getD 0 0) rowsEqual
          have second := congrArg (fun row : List Int => row.getD 1 0) rowsEqual
          have same : actual = pair := Prod.ext (by simpa [PokerGroupOrder.row] using first)
            (by simpa [PokerGroupOrder.row] using second)
          subst actual
          exact .cons ⟨address, rfl, found⟩
            (ih pairs (fun item member => typed item (List.mem_cons_of_mem _ member)) decoded.2)

private theorem context_groups (state : Prepared) (values : List Int) (suits : List String)
    (context : Context state values suits) (extra : Heap) (address : Nat) :
    Context { state with heap := state.heap ++ extra, env := setLocal state.env "sc" (.ref address) } values suits := by
  constructor
  · simpa [setLocal] using context.getRanks
  · simpa [setLocal] using context.getSorted
  · simpa [setLocal] using context.getKeys
  · simpa [setLocal] using context.getFlush
  · simpa [setLocal] using context.getStraight
  · exact groups_found_append context.ranksFound _
  · exact groups_found_append context.sortedFound _
  · exact groups_found_append context.keysFound _

/-- sc is prepared by the actual original rank_counts and sort_counts source calls. -/
theorem prepare_groups (state : Prepared) (values : List Int) (suits : List String)
    (context : Context state values suits) (globals : Mutable.Globals) :
    ∃ next : Prepared, ∃ address : Nat, ∃ groups : List Mutable.Value, ∃ extra : Heap,
      next.heap = state.heap ++ extra ∧
      BlockContinues groupProgram state.env [.assign [.name "sc"] groupExpression]
        state.heap next.env next.heap globals ∧
      Context next values suits ∧
      GroupContext next.heap next.env address groups (counts_key_source.orderedRows values) := by
  let keys := PokerUnique.unique values
  let inputEntries := counts_key_source.countEntries values (state.heap.length+2) keys
  let head := state.heap ++ [.list (groupNumbers keys), .list (counts_source.references (state.heap.length+2) keys)]
  let counted := head ++ counts_source.scratch values keys
  let output := sort_counts_source.sortedRefs counted inputEntries
  let address := (counted ++ sort_counts_source.scratch inputEntries).length
  let final := sort_counts_source.finalHeap counted inputEntries
  let extra := [.list (groupNumbers keys), .list (counts_source.references (state.heap.length+2) keys)] ++
    counts_source.scratch values keys ++ sort_counts_source.scratch inputEntries ++ [.list output]
  have finalShape : final = state.heap ++ extra := by
    simp [final, sort_counts_source.finalHeap, extra, counted, head, output, List.append_assoc]
  have known : sort_counts_source.Found counted inputEntries := by
    have found := entry_known values head keys
    simpa [inputEntries, counted, head] using found
  have countedList : counted[state.heap.length+1]? = some (.list (sort_counts_source.items inputEntries)) := by
    simp [counted, head, inputEntries, entry_items]
  have countRun : Evaluates groupProgram state.env (.call (.name "rank_counts") [.name "rs"])
      state.heap (.ref (state.heap.length+1)) counted globals := by
    apply Evaluates.call (.cons (Evaluates.lookup context.getRanks) .nil)
    simpa [counted, head, keys, List.append_assoc] using counts_source.result values state.heap state.ranksAddress globals context.ranksFound
  have sortRun : Evaluates groupProgram state.env groupExpression state.heap (.ref address) final globals :=
    Evaluates.call (.cons countRun .nil)
      (sort_counts_source.result counted (state.heap.length+1) inputEntries globals countedList known)
  let next : Prepared := { state with heap := final, env := setLocal state.env "sc" (.ref address) }
  refine ⟨next, address, output, extra, finalShape, BlockContinues.assign sortRun, ?_, ?_⟩
  · simpa only [next, finalShape] using context_groups state values suits context extra address
  · constructor
    · simp [next, setLocal]
    · exact sort_counts_source.returned_found counted inputEntries
    · apply rows_of_typed
      · intro value member
        obtain ⟨entry, present, same⟩ := List.mem_map.mp
          ((sort_counts_source.sortedRefs_perm counted inputEntries).mem_iff.mp member)
        exact ⟨entry.address, entry.pair, same.symm, sort_counts_source.caller_found counted inputEntries entry.address _ (known entry present)⟩
      · have rows := sort_counts_source.sortedRefs_rows counted inputEntries known
        simpa [output, inputEntries, keys, entry_pairs, counts_key_source.orderedRows, counts_key_source.countedRows] using rows

end data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

private abbrev assemblyProgram := P54Ast.module
private abbrev assemblyNumber (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev assemblyNumbers (values : List Int) : List Mutable.Value := values.map assemblyNumber
private abbrev assemblyFlag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev assemblyCode := executableBody ((findFunctionIn assemblyProgram.body "hand_score").getD ([], [])).2

def oneCount (pairs : List (Int × Int)) (count : Int) : Bool :=
  !pairs.isEmpty && decide (firstCount pairs = count)
def twoCounts (pairs : List (Int × Int)) (first second : Int) : Bool :=
  decide (2 ≤ pairs.length) && decide (firstCount pairs = first) && decide (secondCount pairs = second)

/-- This definition preserves the exact order and short-circuit guards of the original non-straight-flush suffix. -/
def referenceSuffix (values : List Int) (suits : List String) (pairs : List (Int × Int)) : Int × List Int :=
  if oneCount pairs 4 then (7, counts_key_source.expanded (counts_key_source.orderedRows values))
  else if twoCounts pairs 3 2 then (6, counts_key_source.expanded (counts_key_source.orderedRows values))
  else if flush_source.flush suits then (5, (ScalarSort.ints values).reverse)
  else if PokerStraights.referenceStraight (ScalarSort.ints values) then (4, [straight_high.value values])
  else if oneCount pairs 3 then (3, counts_key_source.expanded (counts_key_source.orderedRows values))
  else if twoCounts pairs 2 2 then (2, counts_key_source.expanded (counts_key_source.orderedRows values))
  else if oneCount pairs 2 then (1, counts_key_source.expanded (counts_key_source.orderedRows values))
  else (0, (ScalarSort.ints values).reverse)

def referenceScore (values : List Int) (suits : List String) : Int × List Int :=
  if PokerStraights.referenceStraight (ScalarSort.ints values) && flush_source.flush suits then
    (straightFlushCategory values, straightFlushKey values)
  else referenceSuffix values suits (counts_key_source.orderedRows values)

private def Scores (env : HeapCalls.Env) (code : List Stmt) (heap : Heap)
    (score : Int × List Int) (globals : Mutable.Globals) : Prop :=
  ∃ extra : Heap, ∃ answer : Mutable.Value,
    BlockReturns assemblyProgram env code heap answer (heap ++ extra) globals ∧
    Represents (heap ++ extra) answer score.1 score.2

private theorem Scores.branch {env : HeapCalls.Env} {heap : Heap} {condition : Expr}
    {yes no following : List Stmt} {value : Mutable.Value} {flag : Bool} {score : Int × List Int}
    {globals : Mutable.Globals}
    (evaluated : Evaluates assemblyProgram env condition heap value heap globals)
    (truth : Mutable.truth value heap = some (.ok flag, heap))
    (selected : Scores env ((if flag then yes else no) ++ following) heap score globals) :
    Scores env (.ifThen condition yes no :: following) heap score globals := by
  obtain ⟨extra, answer, run, represented⟩ := selected
  exact ⟨extra, answer, BlockReturns.branch evaluated truth run, represented⟩

private theorem Scores.existing (state : Prepared) (values : List Int) (suits : List String)
    (context : Context state values suits) (category : Int) (rest : List Stmt) (globals : Mutable.Globals) :
    Scores state.env (.return (.tuple [.constant (.int category), .name "key_counts"]) :: rest) state.heap
      (category, counts_key_source.expanded (counts_key_source.orderedRows values)) globals := by
  obtain ⟨run, represented⟩ := return_existing state.heap state.env category "key_counts" state.keysAddress
    (counts_key_source.expanded (counts_key_source.orderedRows values)) rest globals context.getKeys context.keysFound
  exact ⟨[.tuple [assemblyNumber category, .ref state.keysAddress]], .ref state.heap.length, run, represented⟩

private theorem Scores.reversed (state : Prepared) (values : List Int) (suits : List String)
    (context : Context state values suits) (category : Int) (rest : List Stmt) (globals : Mutable.Globals) :
    Scores state.env (.return (.tuple [.constant (.int category), .reversedList (.name "sorted_rs")]) :: rest) state.heap
      (category, (ScalarSort.ints values).reverse) globals := by
  obtain ⟨run, represented⟩ := return_reversed state.heap state.env category "sorted_rs" state.sortedAddress
    (ScalarSort.ints values) rest globals context.getSorted context.sortedFound
  exact ⟨[.list (assemblyNumbers ((ScalarSort.ints values).reverse)), .tuple [assemblyNumber category, .ref state.heap.length]],
    .ref (state.heap.length+1), run, represented⟩

private theorem Scores.straight (state : Prepared) (values : List Int) (suits : List String)
    (context : Context state values suits) (rest : List Stmt) (globals : Mutable.Globals) :
    Scores state.env
      (.return (.tuple [.constant (.int 4), .list [.call (.name "straight_high") [.name "rs"]]]) :: rest)
      state.heap (4, [straight_high.value values]) globals :=
  return_straight state.heap state.env state.ranksAddress values rest globals context.getRanks context.ranksFound

/-- All non-straight-flush category paths execute their original guards and return the exact reference list key. -/
theorem category_suffix (state : Prepared) (values : List Int) (suits : List String)
    (context : Context state values suits) (address : Nat) (groups : List Mutable.Value) (pairs : List (Int × Int))
    (groupContext : GroupContext state.heap state.env address groups pairs) (globals : Mutable.Globals) :
    ∃ extra : Heap, ∃ answer : Mutable.Value,
      BlockReturns assemblyProgram state.env (assemblyCode.drop 7) state.heap answer (state.heap ++ extra) globals ∧
      Represents (state.heap ++ extra) answer (referenceSuffix values suits pairs).1 (referenceSuffix values suits pairs).2 := by
  change Scores state.env (assemblyCode.drop 7) state.heap (referenceSuffix values suits pairs) globals
  obtain ⟨quadValue, quadEval, quadTruth⟩ := nonempty_count_test state.heap state.env address groups pairs 4 groupContext globals
  obtain ⟨tripleValue, tripleEval, tripleTruth⟩ := nonempty_count_test state.heap state.env address groups pairs 3 groupContext globals
  obtain ⟨pairValue, pairEval, pairTruth⟩ := nonempty_count_test state.heap state.env address groups pairs 2 groupContext globals
  change Mutable.truth quadValue state.heap = some (.ok (oneCount pairs 4), state.heap) at quadTruth
  change Mutable.truth tripleValue state.heap = some (.ok (oneCount pairs 3), state.heap) at tripleTruth
  change Mutable.truth pairValue state.heap = some (.ok (oneCount pairs 2), state.heap) at pairTruth
  have fullEval := two_count_test state.heap state.env address groups pairs 3 2 groupContext globals
  have twoEval := two_count_test state.heap state.env address groups pairs 2 2 groupContext globals
  change Evaluates assemblyProgram state.env _ state.heap (assemblyFlag (twoCounts pairs 3 2)) state.heap globals at fullEval
  change Evaluates assemblyProgram state.env _ state.heap (assemblyFlag (twoCounts pairs 2 2)) state.heap globals at twoEval
  have flushEval : Evaluates assemblyProgram state.env (.name "flush") state.heap
      (assemblyFlag (flush_source.flush suits)) state.heap globals := Evaluates.lookup context.getFlush
  have straightEval : Evaluates assemblyProgram state.env (.name "straight") state.heap
      (assemblyFlag (PokerStraights.referenceStraight (ScalarSort.ints values))) state.heap globals :=
    Evaluates.lookup context.getStraight
  unfold referenceSuffix
  cases quad : oneCount pairs 4 with
  | false =>
      apply Scores.branch (flag := false) quadEval (by simpa only [quad] using quadTruth)
      cases fullHouse : twoCounts pairs 3 2 with
      | false =>
          apply Scores.branch (flag := false) fullEval (by simp [Mutable.truth, scalarTruth, fullHouse])
          cases flush : flush_source.flush suits with
          | false =>
              apply Scores.branch (flag := false) flushEval (by simp [Mutable.truth, scalarTruth, flush])
              cases straight : PokerStraights.referenceStraight (ScalarSort.ints values) with
              | false =>
                  apply Scores.branch (flag := false) straightEval (by simp [Mutable.truth, scalarTruth, straight])
                  cases triple : oneCount pairs 3 with
                  | false =>
                      apply Scores.branch (flag := false) tripleEval (by simpa only [triple] using tripleTruth)
                      cases twoPairs : twoCounts pairs 2 2 with
                      | false =>
                          apply Scores.branch (flag := false) twoEval (by simp [Mutable.truth, scalarTruth, twoPairs])
                          cases pair : oneCount pairs 2 with
                          | false =>
                              apply Scores.branch (flag := false) pairEval (by simpa only [pair] using pairTruth)
                              exact Scores.reversed state values suits context 0 _ globals
                          | true =>
                              apply Scores.branch (flag := true) pairEval (by simpa only [pair] using pairTruth)
                              exact Scores.existing state values suits context 1 _ globals
                      | true =>
                          apply Scores.branch (flag := true) twoEval (by simp [Mutable.truth, scalarTruth, twoPairs])
                          exact Scores.existing state values suits context 2 _ globals
                  | true =>
                      apply Scores.branch (flag := true) tripleEval (by simpa only [triple] using tripleTruth)
                      exact Scores.existing state values suits context 3 _ globals
              | true =>
                  apply Scores.branch (flag := true) straightEval (by simp [Mutable.truth, scalarTruth, straight])
                  exact Scores.straight state values suits context _ globals
          | true =>
              apply Scores.branch (flag := true) flushEval (by simp [Mutable.truth, scalarTruth, flush])
              exact Scores.reversed state values suits context 5 _ globals
      | true =>
          apply Scores.branch (flag := true) fullEval (by simp [Mutable.truth, scalarTruth, fullHouse])
          exact Scores.existing state values suits context 6 _ globals
  | true =>
      apply Scores.branch (flag := true) quadEval (by simpa only [quad] using quadTruth)
      exact Scores.existing state values suits context 7 _ globals

private theorem straight_flush_test (state : Prepared) (values : List Int) (suits : List String)
    (context : Context state values suits) (globals : Mutable.Globals) :
    Evaluates assemblyProgram state.env (.boolOp .and [.name "straight", .name "flush"]) state.heap
      (assemblyFlag (PokerStraights.referenceStraight (ScalarSort.ints values) && flush_source.flush suits)) state.heap globals := by
  cases straight : PokerStraights.referenceStraight (ScalarSort.ints values) with
  | false =>
      exact Evaluates.boolean_stop (flag := false) (by simpa only [straight] using Evaluates.lookup context.getStraight) rfl rfl
  | true =>
      exact Evaluates.boolean_next (flag := true) (by simpa only [straight] using Evaluates.lookup context.getStraight) rfl rfl
        (Evaluates.boolean_last (flag := flush_source.flush suits) (Evaluates.lookup context.getFlush) rfl)

/-- The non-straight-flush path executes the second counting/sorting preparation and all original category branches. -/
theorem non_straight_flush_suffix (state : Prepared) (values : List Int) (suits : List String)
    (context : Context state values suits) (globals : Mutable.Globals)
    (notBoth : (PokerStraights.referenceStraight (ScalarSort.ints values) && flush_source.flush suits) = false) :
    ∃ extra : Heap, ∃ answer : Mutable.Value,
      BlockReturns assemblyProgram state.env (assemblyCode.drop 5) state.heap answer (state.heap ++ extra) globals ∧
      Represents (state.heap ++ extra) answer
        (referenceSuffix values suits (counts_key_source.orderedRows values)).1
        (referenceSuffix values suits (counts_key_source.orderedRows values)).2 := by
  obtain ⟨next, address, groups, groupExtra, shape, prepared, nextContext, groupContext⟩ :=
    prepare_groups state values suits context globals
  obtain ⟨categoryExtra, answer, categories, represented⟩ :=
    category_suffix next values suits nextContext address groups (counts_key_source.orderedRows values) groupContext globals
  have afterGroups : BlockReturns assemblyProgram state.env (assemblyCode.drop 6) state.heap answer
      (next.heap ++ categoryExtra) globals := prepared.returns categories
  have tested := straight_flush_test state values suits context globals
  have testedFalse : Evaluates assemblyProgram state.env (.boolOp .and [.name "straight", .name "flush"])
      state.heap (assemblyFlag false) state.heap globals := by simpa only [notBoth] using tested
  have returned : BlockReturns assemblyProgram state.env (assemblyCode.drop 5) state.heap answer
      (next.heap ++ categoryExtra) globals :=
    BlockReturns.branch (value := assemblyFlag false) (flag := false) testedFalse rfl afterGroups
  refine ⟨groupExtra ++ categoryExtra, answer, ?_, ?_⟩
  · simpa only [shape, List.append_assoc] using returned
  · simpa only [shape, List.append_assoc] using represented

/-- Full reference hand_score source correctness for live rank valuations and arbitrary finite token lists. -/
theorem result (heap : Heap) (address tableAddress : Nat) (cards : List flush_source.Card)
    (valuation : flush_source.Card → Int) (table : List (Constant × Mutable.Value)) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (flush_source.tokens cards)))
    (tableFound : heap[tableAddress]? = some (.dict table))
    (getTable : globals.lookup "rank_values" = some (.ref tableAddress))
    (valued : ∀ card ∈ cards, ScalarDict.lookup table (.string (String.singleton card.rankChar)) =
      some (assemblyNumber (valuation card))) :
    ∃ extra : Heap, ∃ answer : Mutable.Value,
      ReturnsValue assemblyProgram "hand_score" [.ref address] heap answer (heap ++ extra) globals ∧
      Represents (heap ++ extra) answer (referenceScore (cards.map valuation) (flush_source.suits cards)).1
        (referenceScore (cards.map valuation) (flush_source.suits cards)).2 := by
  obtain ⟨state, prefixExtra, shape, prepared, context⟩ := prepare heap address tableAddress cards valuation table globals
    found tableFound getTable valued
  cases both : PokerStraights.referenceStraight (ScalarSort.ints (cards.map valuation)) &&
      flush_source.flush (flush_source.suits cards) with
  | false =>
      obtain ⟨suffixExtra, answer, suffix, represented⟩ := non_straight_flush_suffix state (cards.map valuation)
        (flush_source.suits cards) context globals both
      refine ⟨prefixExtra ++ suffixExtra, answer, ?_, ?_⟩
      · simpa only [shape, List.append_assoc] using
          result_of_suffix heap address state answer (state.heap ++ suffixExtra) globals prepared suffix
      · simpa [referenceScore, both, shape, List.append_assoc] using represented
  | true =>
      have straight : PokerStraights.referenceStraight (ScalarSort.ints (cards.map valuation)) = true := (Bool.and_eq_true_iff.mp both).1
      have flush : flush_source.flush (flush_source.suits cards) = true := (Bool.and_eq_true_iff.mp both).2
      obtain ⟨suffixExtra, answer, suffix, represented⟩ := straight_flush_suffix state (cards.map valuation)
        (flush_source.suits cards) context globals straight flush
      refine ⟨prefixExtra ++ suffixExtra, answer, ?_, ?_⟩
      · simpa only [shape, List.append_assoc] using
          result_of_suffix heap address state answer (state.heap ++ suffixExtra) globals prepared suffix
      · simpa [referenceScore, both, shape, List.append_assoc] using represented

end data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source
open FormalSW.PyAst

/-- Appending private objects preserves an already returned reference score. -/
theorem Represents.append {heap : Mutable.Heap} {value : Mutable.Value} {category : Int} {key : List Int}
    (represented : Represents heap value category key) (extra : Mutable.Heap) :
    Represents (heap ++ extra) value category key := by
  obtain ⟨tupleAddress, listAddress, rfl, tupleFound, listFound⟩ := represented
  exact ⟨tupleAddress, listAddress, rfl,
    ProjectEulerSolutions.HeapCollection.prefix_found _ extra _ _ tupleFound,
    ProjectEulerSolutions.HeapCollection.prefix_found _ extra _ _ listFound⟩

end data.«project-euler-statements».data.py.project_euler_statements.p54.hand_score_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.beats_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.PokerTiebreaks
set_option Elab.async false

private abbrev program := P54Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev numbers (values : List Int) : List Mutable.Value := values.map number
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev params := ((findFunctionIn program.body "beats").getD ([], [])).1
private abbrev body := ((findFunctionIn program.body "beats").getD ([], [])).2
private abbrev initial (globals : Mutable.Globals) (left right : Mutable.Value) : HeapCalls.Env :=
  functionEnv params body [left, right] globals
private abbrev component (name : String) (index : Int) : Expr :=
  .subscript (.name name) (.constant (.int index))
private abbrev returnExpression : Expr :=
  .ifExp (.compare (component "s1" 0) [(.eq, component "s2" 0)])
    (.call (.name "lex_gt") [component "s1" 1, component "s2" 1])
    (.compare (component "s1" 0) [(.gt, component "s2" 0)])

def greater (leftCategory rightCategory : Int) (leftKey rightKey : List Int) : Bool :=
  if leftCategory = rightCategory then referenceGreater leftKey rightKey else decide (rightCategory < leftCategory)

private theorem category_eval (heap : Heap) (env : HeapCalls.Env) (name : String) (tupleAddress listAddress : Nat)
    (category : Int) (globals : Mutable.Globals)
    (bound : env name = some (.ref tupleAddress))
    (found : heap[tupleAddress]? = some (.tuple [number category, .ref listAddress])) :
    Evaluates program env (component name 0) heap (number category) heap globals := by
  apply Evaluates.subscript (by intros; simp) (Evaluates.lookup bound) Evaluates.constant
  simp [Mutable.getItem, Mutable.index, found, number, Except.map]

private theorem key_eval (heap : Heap) (env : HeapCalls.Env) (name : String) (tupleAddress listAddress : Nat)
    (category : Int) (globals : Mutable.Globals)
    (bound : env name = some (.ref tupleAddress))
    (found : heap[tupleAddress]? = some (.tuple [number category, .ref listAddress])) :
    Evaluates program env (component name 1) heap (.ref listAddress) heap globals := by
  apply Evaluates.subscript (by intros; simp) (Evaluates.lookup bound) Evaluates.constant
  simp [Mutable.getItem, Mutable.index, found, number, Except.map]

/-- The exact source comparison composes two hand-score calls and retains the outer unpacking tuple.
Equal categories execute the original recursive lex_gt on arbitrary integer keys, including unequal lengths. -/
theorem result (heap middle finalHeap : Heap) (leftHand rightHand leftScore rightScore : Mutable.Value)
    (leftCategory rightCategory : Int) (leftKey rightKey : List Int) (globals : Mutable.Globals)
    (first : ReturnsValue program "hand_score" [leftHand] heap leftScore middle globals)
    (second : ReturnsValue program "hand_score" [rightHand] middle rightScore finalHeap globals)
    (leftRep : hand_score_source.Represents finalHeap leftScore leftCategory leftKey)
    (rightRep : hand_score_source.Represents finalHeap rightScore rightCategory rightKey) :
    ∃ extra, ReturnsValue program "beats" [leftHand, rightHand] heap
      (flag (greater leftCategory rightCategory leftKey rightKey))
      ((finalHeap ++ [.tuple [leftScore, rightScore]]) ++ extra) globals := by
  obtain ⟨leftAddress, leftListAddress, rfl, leftTuple, leftList⟩ := leftRep
  obtain ⟨rightAddress, rightListAddress, rfl, rightTuple, rightList⟩ := rightRep
  let start := initial globals leftHand rightHand
  let ready := assignNames start ["s1", "s2"] [.ref leftAddress, .ref rightAddress]
  let paired := finalHeap ++ [.tuple [.ref leftAddress, .ref rightAddress]]
  have getLeftHand : start "h1" = some leftHand := by cases globals <;> rfl
  have getRightHand : start "h2" = some rightHand := by cases globals <;> rfl
  have getLeftScore : ready "s1" = some (.ref leftAddress) := by simp [ready, assignNames, setLocal]
  have getRightScore : ready "s2" = some (.ref rightAddress) := by simp [ready, assignNames, setLocal]
  have tupleDisplay : Evaluates program start
      (.tuple [.call (.name "hand_score") [.name "h1"], .call (.name "hand_score") [.name "h2"]])
      heap (.ref finalHeap.length) paired globals := by
    exact Evaluates.tuple
      (.cons (Evaluates.call (.cons (Evaluates.lookup getLeftHand) .nil) first)
        (.cons (Evaluates.call (.cons (Evaluates.lookup getRightHand) .nil) second) .nil)) (by simp)
  have leftTupleKept : paired[leftAddress]? = some (.tuple [number leftCategory, .ref leftListAddress]) :=
    ProjectEulerSolutions.HeapCollection.prefix_found _ _ _ _ leftTuple
  have rightTupleKept : paired[rightAddress]? = some (.tuple [number rightCategory, .ref rightListAddress]) :=
    ProjectEulerSolutions.HeapCollection.prefix_found _ _ _ _ rightTuple
  have leftListKept : paired[leftListAddress]? = some (.list (numbers leftKey)) :=
    ProjectEulerSolutions.HeapCollection.prefix_found _ _ _ _ leftList
  have rightListKept : paired[rightListAddress]? = some (.list (numbers rightKey)) :=
    ProjectEulerSolutions.HeapCollection.prefix_found _ _ _ _ rightList
  have leftCategoryEval := category_eval paired ready "s1" leftAddress leftListAddress leftCategory globals getLeftScore leftTupleKept
  have rightCategoryEval := category_eval paired ready "s2" rightAddress rightListAddress rightCategory globals getRightScore rightTupleKept
  have equality : Evaluates program ready (.compare (component "s1" 0) [(.eq, component "s2" 0)]) paired
      (flag (decide (leftCategory = rightCategory))) paired globals := by
    apply Evaluates.compare leftCategoryEval rightCategoryEval
    simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag]
  have finish (answer : Mutable.Value) (last : Heap)
      (evaluated : Evaluates program ready returnExpression paired answer last globals) :
      ReturnsValue program "beats" [leftHand, rightHand] heap answer last globals := by
    apply BlockReturns.function rfl rfl
    apply BlockReturns.unpack (names := ["s1", "s2"]) (items := [.ref leftAddress, .ref rightAddress])
      (middle := paired) (afterUnpack := paired) rfl tupleDisplay (by simp [paired, Mutable.sequence]) rfl
    exact BlockReturns.return_value evaluated
  by_cases same : leftCategory = rightCategory
  · obtain ⟨extra, compared⟩ := lex_gt.result (globals := globals) leftKey rightKey paired
      leftListAddress rightListAddress leftListKept rightListKept
    refine ⟨extra, ?_⟩
    apply finish
    apply Evaluates.conditional (flag := true) (value := flag true) (middle := paired)
    · simpa [same] using equality
    · rfl
    · simpa only [greater, if_pos same] using Evaluates.call
        (.cons (key_eval paired ready "s1" leftAddress leftListAddress leftCategory globals getLeftScore leftTupleKept)
          (.cons (key_eval paired ready "s2" rightAddress rightListAddress rightCategory globals getRightScore rightTupleKept) .nil)) compared
  · refine ⟨[], ?_⟩
    simp only [List.append_nil]
    apply finish
    apply Evaluates.conditional (flag := false) (value := flag false) (middle := paired)
    · simpa [same] using equality
    · rfl
    · simp only [greater, if_neg same]
      apply Evaluates.compare leftCategoryEval rightCategoryEval
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, flag, paired]

end data.«project-euler-statements».data.py.project_euler_statements.p54.beats_source

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.beats_source.total
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
set_option Elab.async false

private abbrev program := P54Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)

def score (cards : List flush_source.Card) (valuation : flush_source.Card → Int) : Int × List Int :=
  hand_score_source.referenceScore (cards.map valuation) (flush_source.suits cards)

def wins (left right : List flush_source.Card) (valuation : flush_source.Card → Int) : Bool :=
  beats_source.greater (score left valuation).1 (score right valuation).1
    (score left valuation).2 (score right valuation).2

/-- Both original hand evaluators and the complete reference comparison execute with the caller's live rank dictionary. -/
theorem result (heap : Heap) (leftAddress rightAddress tableAddress : Nat)
    (left right : List flush_source.Card) (valuation : flush_source.Card → Int)
    (table : List (Constant × Mutable.Value)) (globals : Mutable.Globals)
    (leftFound : heap[leftAddress]? = some (.list (flush_source.tokens left)))
    (rightFound : heap[rightAddress]? = some (.list (flush_source.tokens right)))
    (tableFound : heap[tableAddress]? = some (.dict table))
    (getTable : globals.lookup "rank_values" = some (.ref tableAddress))
    (leftValued : ∀ card ∈ left, ScalarDict.lookup table (.string (String.singleton card.rankChar)) =
      some (number (valuation card)))
    (rightValued : ∀ card ∈ right, ScalarDict.lookup table (.string (String.singleton card.rankChar)) =
      some (number (valuation card))) :
    ∃ extra, ReturnsValue program "beats" [.ref leftAddress, .ref rightAddress] heap
      (flag (wins left right valuation)) (heap ++ extra) globals := by
  obtain ⟨leftExtra, leftScore, leftRun, leftRep⟩ := hand_score_source.result heap leftAddress tableAddress
    left valuation table globals leftFound tableFound getTable leftValued
  have retainedRight : (heap ++ leftExtra)[rightAddress]? = some (.list (flush_source.tokens right)) :=
    ProjectEulerSolutions.HeapCollection.prefix_found _ leftExtra _ _ rightFound
  have retainedTable : (heap ++ leftExtra)[tableAddress]? = some (.dict table) :=
    ProjectEulerSolutions.HeapCollection.prefix_found _ leftExtra _ _ tableFound
  obtain ⟨rightExtra, rightScore, rightRun, rightRep⟩ := hand_score_source.result (heap ++ leftExtra)
    rightAddress tableAddress right valuation table globals retainedRight retainedTable getTable rightValued
  have retainedLeft := leftRep.append rightExtra
  obtain ⟨comparisonExtra, compared⟩ := beats_source.result heap (heap ++ leftExtra)
    ((heap ++ leftExtra) ++ rightExtra) (.ref leftAddress) (.ref rightAddress) leftScore rightScore
    (score left valuation).1 (score right valuation).1 (score left valuation).2 (score right valuation).2
    globals leftRun rightRun retainedLeft rightRep
  refine ⟨leftExtra ++ rightExtra ++ [.tuple [leftScore, rightScore]] ++ comparisonExtra, ?_⟩
  simpa only [wins, List.append_assoc] using compared

end data.«project-euler-statements».data.py.project_euler_statements.p54.beats_source.total

namespace data.«project-euler-statements».data.py.project_euler_statements.p54.naive_source
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
set_option Elab.async false

private abbrev program := P54Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev Card := flush_source.Card

structure Deal where
  pairAddress : Nat
  leftAddress : Nat
  rightAddress : Nat
  leftCards : List Card
  rightCards : List Card

def Deal.Found (heap : Heap) (deal : Deal) : Prop :=
  heap[deal.pairAddress]? = some (.tuple [.ref deal.leftAddress, .ref deal.rightAddress]) ∧
    heap[deal.leftAddress]? = some (.list (flush_source.tokens deal.leftCards)) ∧
    heap[deal.rightAddress]? = some (.list (flush_source.tokens deal.rightCards))

def Deal.Valued (table : List (Constant × Mutable.Value)) (valuation : Card → Int) (deal : Deal) : Prop :=
  (∀ card ∈ deal.leftCards, ScalarDict.lookup table (.string (String.singleton card.rankChar)) = some (number (valuation card))) ∧
  (∀ card ∈ deal.rightCards, ScalarDict.lookup table (.string (String.singleton card.rankChar)) = some (number (valuation card)))

theorem Deal.Found.append {heap : Heap} {deal : Deal} (known : deal.Found heap) (extra : Heap) :
    deal.Found (heap ++ extra) :=
  ⟨ProjectEulerSolutions.HeapCollection.prefix_found _ extra _ _ known.1,
    ProjectEulerSolutions.HeapCollection.prefix_found _ extra _ _ known.2.1,
    ProjectEulerSolutions.HeapCollection.prefix_found _ extra _ _ known.2.2⟩

def weight (valuation : Card → Int) (deal : Deal) : Int :=
  if beats_source.total.wins deal.leftCards deal.rightCards valuation then 1 else 0

def total (valuation : Card → Int) : List Deal → Int
  | [] => 0
  | deal :: deals => weight valuation deal + total valuation deals

def items (deals : List Deal) : List Mutable.Value := deals.map fun deal => .ref deal.pairAddress

private abbrev target : Expr := .tuple [.name "h1", .name "h2"]
private abbrev tested : Expr := .call (.name "beats") [.name "h1", .name "h2"]
private abbrev filterBody : List Stmt := [.ifThen tested (sumBody (.constant (.int 1)) []) []]
private abbrev loopBody : List Stmt :=
  .assign [target] (.name "$formalsw.unpack") :: filterBody

/-- Each input pair is unpacked before the real beats filter runs. -/
private theorem body_step (deal : Deal) (heap : Heap) (env : HeapCalls.Env) (initial : Int)
    (valuation : Card → Int) (globals : Mutable.Globals) (tableAddress : Nat)
    (table : List (Constant × Mutable.Value)) (known : deal.Found heap) (valued : deal.Valued table valuation)
    (getTable : globals.lookup "rank_values" = some (.ref tableAddress))
    (tableFound : heap[tableAddress]? = some (.dict table))
    (getPair : env "$formalsw.unpack" = some (.ref deal.pairAddress))
    (accumulator : env sumAccumulator = some (number initial)) :
    ∃ extra finalEnv, BlockContinues program env loopBody heap finalEnv (heap ++ extra) globals ∧
      finalEnv sumAccumulator = some (number (initial + weight valuation deal)) := by
  let ready := assignNames env ["h1", "h2"] [.ref deal.leftAddress, .ref deal.rightAddress]
  have getLeft : ready "h1" = some (.ref deal.leftAddress) := by simp [ready, assignNames, setLocal]
  have getRight : ready "h2" = some (.ref deal.rightAddress) := by simp [ready, assignNames, setLocal]
  have readyAccumulator : ready sumAccumulator = some (number initial) := by
    simpa [ready, assignNames, setLocal, sumAccumulator] using accumulator
  have unpacked : BlockContinues program env [.assign [target] (.name "$formalsw.unpack")] heap ready heap globals :=
    BlockContinues.unpack rfl (Evaluates.lookup getPair) (by simp [Mutable.sequence, known.1]) rfl
  obtain ⟨extra, ran⟩ := beats_source.total.result heap deal.leftAddress deal.rightAddress tableAddress
    deal.leftCards deal.rightCards valuation table globals known.2.1 known.2.2 tableFound getTable valued.1 valued.2
  have evaluated : Evaluates program ready tested heap
      (flag (beats_source.total.wins deal.leftCards deal.rightCards valuation)) (heap ++ extra) globals :=
    Evaluates.call (.cons (Evaluates.lookup getLeft) (.cons (Evaluates.lookup getRight) .nil)) ran
  cases winning : beats_source.total.wins deal.leftCards deal.rightCards valuation with
  | false =>
      have filtered : BlockContinues program ready filterBody heap ready (heap ++ extra) globals := by
        apply BlockContinues.branch (flag := false) (by simpa only [winning] using evaluated) rfl
        exact BlockContinues.nil
      refine ⟨extra, ready, unpacked.append filtered, ?_⟩
      simpa only [weight, winning, Bool.false_eq_true, ↓reduceIte, Int.add_zero] using readyAccumulator
  | true =>
      have filtered : BlockContinues program ready filterBody heap
          (setLocal ready sumAccumulator (number (initial+1))) (heap ++ extra) globals := by
        apply BlockContinues.branch (flag := true) (by simpa only [winning] using evaluated) rfl
        apply BlockContinues.assign
        exact Evaluates.binary (Evaluates.lookup readyAccumulator) Evaluates.constant rfl
      refine ⟨extra, _, unpacked.append filtered, ?_⟩
      simp [weight, winning, setLocal]

private theorem loop (deals remaining : List Deal) (heap : Heap) (address : Nat)
    (found : heap[address]? = some (.list (items deals))) (position : Nat)
    (suffix : deals.drop position = remaining) (env : HeapCalls.Env) (initial : Int)
    (accumulator : env sumAccumulator = some (number initial))
    (valuation : Card → Int) (globals : Mutable.Globals) (tableAddress : Nat)
    (table : List (Constant × Mutable.Value)) (getTable : globals.lookup "rank_values" = some (.ref tableAddress))
    (tableFound : heap[tableAddress]? = some (.dict table))
    (known : ∀ deal ∈ deals, deal.Found heap) (valued : ∀ deal ∈ deals, deal.Valued table valuation) :
    ∃ extra, BlockReturns program env
      [.sequenceStepLoop "$formalsw.unpack" (.ref address) position loopBody [], .return (.name sumAccumulator)]
      heap (number (initial + total valuation remaining)) (heap ++ extra) globals := by
  induction remaining generalizing heap position env initial with
  | nil =>
      have missing : deals[position]? = none := by
        simpa [suffix] using (List.head?_drop (l := deals) (i := position)).symm
      refine ⟨[], ?_⟩
      simp only [List.append_nil, total, Int.add_zero]
      apply BlockReturns.sequence_done (source := .ref address) (items := items deals)
        (by simp [sequenceValue, Mutable.sequence, found])
        (by simp only [items, List.getElem?_map, missing, Option.map_none])
      exact BlockReturns.return_value (Evaluates.lookup accumulator)
  | cons deal rest ih =>
      have item : deals[position]? = some deal := by
        simpa [suffix] using (List.head?_drop (l := deals) (i := position)).symm
      have member : deal ∈ deals := List.mem_of_getElem? item
      let ready := setLocal env "$formalsw.unpack" (.ref deal.pairAddress)
      have readyAccumulator : ready sumAccumulator = some (number initial) := by
        simpa [ready, setLocal, sumAccumulator] using accumulator
      obtain ⟨firstExtra, finalEnv, stepped, nextAccumulator⟩ := body_step deal heap ready initial valuation globals
        tableAddress table (known deal member) (valued deal member) getTable tableFound rfl readyAccumulator
      have retainedInput : (heap ++ firstExtra)[address]? = some (.list (items deals)) :=
        ProjectEulerSolutions.HeapCollection.prefix_found _ firstExtra _ _ found
      have retainedTable : (heap ++ firstExtra)[tableAddress]? = some (.dict table) :=
        ProjectEulerSolutions.HeapCollection.prefix_found _ firstExtra _ _ tableFound
      have retainedDeals : ∀ selected ∈ deals, selected.Found (heap ++ firstExtra) :=
        fun selected present => (known selected present).append firstExtra
      obtain ⟨restExtra, continued⟩ := ih (heap ++ firstExtra) retainedInput (position+1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) finalEnv (initial + weight valuation deal)
        nextAccumulator retainedTable retainedDeals
      refine ⟨firstExtra ++ restExtra, ?_⟩
      apply BlockReturns.sequence_step (source := .ref address) (value := .ref deal.pairAddress) (items := items deals)
        (by simp [sequenceValue, Mutable.sequence, found])
        (by simp only [items, List.getElem?_map, item, Option.map_some])
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, loopBody, filterBody, sumBody,
        total, Int.add_assoc, List.append_assoc] using stepped.returns continued

private abbrev params := ((findFunctionIn program.body "naive").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "naive").getD ([], [])).2
private abbrev entry (globals : Mutable.Globals) (address : Nat) : HeapCalls.Env :=
  functionEnv params sourceBody [.ref address] globals

/-- The original unpacking/filtering generator counts the complete reference beats results for arbitrary finite inputs. -/
theorem result (deals : List Deal) (heap : Heap) (address : Nat)
    (found : heap[address]? = some (.list (items deals)))
    (valuation : Card → Int) (globals : Mutable.Globals) (tableAddress : Nat)
    (table : List (Constant × Mutable.Value)) (getTable : globals.lookup "rank_values" = some (.ref tableAddress))
    (tableFound : heap[tableAddress]? = some (.dict table))
    (known : ∀ deal ∈ deals, deal.Found heap) (valued : ∀ deal ∈ deals, deal.Valued table valuation) :
    ∃ extra, ReturnsValue program "naive" [.ref address] heap (number (total valuation deals)) (heap ++ extra) globals := by
  have getHands : entry globals address "hands" = some (.ref address) := by cases globals <;> rfl
  let inside := setLocal
    (comprehensionTargetsEnv (entry globals address) [(target, .name "hands", [tested])]) sumAccumulator (number 0)
  obtain ⟨extra, ran⟩ := loop deals deals heap address found 0 rfl inside 0 (by simp [inside, setLocal])
    valuation globals tableAddress table getTable tableFound known valued
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_targets_sequence (target := target) (filters := [tested]) (generators := [])
    (items := items deals)
    (by intro expressions impossible; cases impossible) (by intro expressions impossible; cases impossible)
    (by intro expressions impossible; cases impossible)
    (Evaluates.lookup getHands) (by simp [Mutable.sequence, found]) Evaluates.constant rfl
  simpa only [inside, comprehensionTargetName, comprehensionTargetBody, comprehensionFilters, comprehensionTargetsBody,
    target, filterBody, loopBody, sumBody, List.foldr_cons, List.foldr_nil, Int.zero_add] using ran

end data.«project-euler-statements».data.py.project_euler_statements.p54.naive_source
