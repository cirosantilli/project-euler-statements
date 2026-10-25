import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p54.py.ast»
import ProjectEulerSolutions.Lib.PokerTiebreaks
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
