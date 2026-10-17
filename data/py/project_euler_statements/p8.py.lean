import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p8.py.ast»
import FormalSW
import ProjectEulerStatements.P8
import Mathlib.Tactic

namespace data.«project-euler-statements».data.py.project_euler_statements.p8
open FormalSW.PyAst
private abbrev program := P8Ast.module
private abbrev productBody : List Stmt := [.augAssign (.name "p") .mult (.name "x")]
private def ints (xs : List Int) : List Mutable.Value := xs.map fun x => .scalar (.int x)

/-- A product loop preserves its input heap, including all aliases to that list. -/
private theorem product.loop (remaining : List Int) (before : List Int) (heap : Mutable.Heap)
    (address : Nat) (found : heap[address]? = some (.list (ints (before ++ remaining))))
    (env : HeapCalls.Env) (acc : Int) (hp : env "p" = some (.scalar (.int acc))) :
    HeapCalls.BlockReturns program env
      [.sequenceStepLoop "x" (.ref address) before.length productBody [], .return (.name "p")]
      heap (.scalar (.int (acc * remaining.prod))) heap := by
  induction remaining generalizing before env acc with
  | nil =>
      apply HeapCalls.BlockReturns.sequence_done (items := ints before)
      · simp only [List.append_nil] at found
        simp [HeapCalls.sequenceValue, Mutable.sequence, found]
      · simp [ints]
      · simpa [List.prod_nil] using HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup hp)
  | cons value rest ih =>
      apply HeapCalls.BlockReturns.sequence_step (items := ints (before ++ value :: rest)) (value := .scalar (.int value))
      · simp [HeapCalls.sequenceValue, Mutable.sequence, found]
      · simp [ints]
      · apply HeapCalls.BlockReturns.augAssign (by simpa [HeapCalls.setLocal] using hp)
          (HeapCalls.Evaluates.lookup rfl) (middle := heap) (afterOperation := heap) (right := .scalar (.int value))
          (value := .scalar (.int (acc * value)))
        · rfl
        · have next := ih (before ++ [value]) (by simpa [List.append_assoc] using found)
            (HeapCalls.setLocal (HeapCalls.setLocal env "x" (.scalar (.int value)))
              "p" (.scalar (.int (acc * value)))) (acc * value) rfl
          simpa [productBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            List.length_append, List.prod_cons, Int.mul_assoc] using next

theorem list_product.result (xs : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (ints xs))) :
    HeapCalls.ReturnsValue program "list_product" [.ref address] heap (.scalar (.int (xs.prod))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  apply HeapCalls.BlockReturns.for_sequence (by intro expressions; simp)
    (HeapCalls.Evaluates.lookup rfl) (items := ints xs)
  · simp [Mutable.sequence, found]
  · let env := HeapCalls.setLocal
      (HeapCalls.argumentEnv [{ name := "xs", annotation := some (.subscript (.name "list") (.name "int")) }]
        [.ref address]) "p" (.scalar (.int 1))
    simpa using product.loop xs [] heap address (by simpa using found) env 1 rfl

private theorem product_cast (xs : List Nat) :
    (xs.map Int.ofNat).prod = (ProjectEulerStatements.P8.listProduct xs : Int) := by
  induction xs with
  | nil => simp [ProjectEulerStatements.P8.listProduct]
  | cons head tail ih => simp [ProjectEulerStatements.P8.listProduct, ih]

/-- The existing natural-number specification agrees with the Python integer product. -/
theorem list_product.naturals (xs : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (ints (xs.map Int.ofNat)))) :
    HeapCalls.ReturnsValue program "list_product" [.ref address] heap
      (.scalar (.int (ProjectEulerStatements.P8.listProduct xs))) heap := by
  simpa [product_cast] using list_product.result (xs.map Int.ofNat) heap address found

private abbrev maximumBody : List Stmt :=
  [.assign [.name "m"] (.builtinCall .max [.name "m", .name "x"])]

private theorem maximum_operation (a b : Int) (heap : Mutable.Heap) :
    HeapCalls.primitive (.builtin .max) [.scalar (.int a), .scalar (.int b)] heap =
      some (.ok (.scalar (.int (max a b))), heap) := by
  simp [HeapCalls.primitive, HeapCalls.scalarResult, Calls.positionalMaximum,
    Calls.maximumFrom, scalarCompare, evalCmpOp, max_def]
  split <;> split <;> simp_all <;> omega

private theorem maximum.loop (remaining before : List Int) (heap : Mutable.Heap)
    (address : Nat) (found : heap[address]? = some (.list (ints (before ++ remaining))))
    (env : HeapCalls.Env) (acc : Int) (hm : env "m" = some (.scalar (.int acc))) :
    HeapCalls.BlockReturns program env
      [.sequenceStepLoop "x" (.ref address) before.length maximumBody [], .return (.name "m")]
      heap (.scalar (.int (remaining.foldl max acc))) heap := by
  induction remaining generalizing before env acc with
  | nil =>
      apply HeapCalls.BlockReturns.sequence_done (items := ints before)
      · simp only [List.append_nil] at found
        simp [HeapCalls.sequenceValue, Mutable.sequence, found]
      · simp [ints]
      · exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup hm)
  | cons value rest ih =>
      apply HeapCalls.BlockReturns.sequence_step
        (items := ints (before ++ value :: rest)) (value := .scalar (.int value))
      · simp [HeapCalls.sequenceValue, Mutable.sequence, found]
      · simp [ints]
      · apply HeapCalls.BlockReturns.assign
        · exact HeapCalls.Evaluates.builtin
            (.cons (HeapCalls.Evaluates.lookup (by simpa [HeapCalls.setLocal] using hm))
              (.cons (HeapCalls.Evaluates.lookup rfl) .nil)) (maximum_operation acc value heap)
        · have next := ih (before ++ [value]) (by simpa [List.append_assoc] using found)
            (HeapCalls.setLocal (HeapCalls.setLocal env "x" (.scalar (.int value)))
              "m" (.scalar (.int (max acc value)))) (max acc value) rfl
          simpa [maximumBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            List.length_append] using next

theorem list_max.result (xs : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (ints xs))) :
    HeapCalls.ReturnsValue program "list_max" [.ref address] heap
      (.scalar (.int (xs.foldl max 0))) heap := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign HeapCalls.Evaluates.constant
  apply HeapCalls.BlockReturns.for_sequence (by intro expressions; simp)
    (HeapCalls.Evaluates.lookup rfl) (items := ints xs)
  · simp [Mutable.sequence, found]
  · let env := HeapCalls.setLocal
      (HeapCalls.argumentEnv [{ name := "xs", annotation := some (.subscript (.name "list") (.name "int")) }]
        [.ref address]) "m" (.scalar (.int 0))
    exact maximum.loop xs [] heap address found env 0 rfl

private theorem maximum_cast (xs : List Nat) (initial : Nat) :
    (xs.map Int.ofNat).foldl max (initial : Int) = (max initial (ProjectEulerStatements.P8.listMax xs) : Nat) := by
  induction xs generalizing initial with
  | nil => simp [ProjectEulerStatements.P8.listMax]
  | cons head tail ih =>
      simp only [List.map_cons, List.foldl_cons]
      have start : max (initial : Int) (Int.ofNat head) = (max initial head : Nat) := by
        simp [Int.ofNat_eq_natCast]
      rw [start, ih]
      simp [ProjectEulerStatements.P8.listMax, max_assoc]

/-- The maximum loop agrees with the existing specification on natural inputs. -/
theorem list_max.naturals (xs : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (ints (xs.map Int.ofNat)))) :
    HeapCalls.ReturnsValue program "list_max" [.ref address] heap
      (.scalar (.int (ProjectEulerStatements.P8.listMax xs))) heap := by
  have result := list_max.result (xs.map Int.ofNat) heap address found
  have value : (xs.map Int.ofNat).foldl max 0 = (ProjectEulerStatements.P8.listMax xs : Int) := by
    simpa using maximum_cast xs 0
  simpa only [value] using result

/-- Integer-index slicing gives a total version of the window specification. -/
def windowValues (k : Int) : List Int → List Int
  | [] => []
  | head :: tail =>
      if ((head :: tail).length : Int) < k then []
      else ((head :: tail).take (FormalSW.Py.Builtin.Slice.prefixLength (head :: tail).length k)).prod ::
        windowValues k tail

/-- Natural inputs recover the existing Project Euler window specification. -/
theorem windowValues_cast (k : Nat) (xs : List Nat) :
    windowValues k (xs.map Int.ofNat) = (ProjectEulerStatements.P8.windowProducts k xs).map Int.ofNat := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      have guard : (tail.length : Int) + 1 < (k : Int) ↔ tail.length + 1 < k := by omega
      by_cases short : tail.length + 1 < k
      · simp [windowValues, ProjectEulerStatements.P8.windowProducts, guard, short]
      · have enough : k ≤ tail.length + 1 := by omega
        have product := product_cast ((head :: tail).take k)
        simp only [List.map_take, List.map_cons, Int.ofNat_eq_natCast] at product
        simp [windowValues, ProjectEulerStatements.P8.windowProducts, guard, short,
          FormalSW.Py.Builtin.Slice.prefixLength_nonnegative, min_eq_left enough, product, ih]

private theorem lookup_extended {before after : Mutable.Heap} {address : Nat} {object : Mutable.Object} (selected : before <+: after)
    (found : before[address]? = some object) : after[address]? = some object := by
  obtain ⟨extra, rfl⟩ := selected
  have valid : address < before.length := List.getElem?_eq_some_iff.mp found |>.1
  simpa [List.getElem?_append, valid] using found

private theorem window.empty_test (env : HeapCalls.Env) (xs : List Int) (heap : Mutable.Heap) (address : Nat)
    (lookup : env "xs" = some (.ref address)) (found : heap[address]? = some (.list (ints xs))) :
    HeapCalls.Evaluates program env (.unaryOp .not (.name "xs")) heap (.scalar (.bool xs.isEmpty)) heap := by
  apply HeapCalls.Evaluates.unary (HeapCalls.Evaluates.lookup lookup)
  simp [HeapCalls.unary, Mutable.truth, found, ints]

private theorem window.short_test (env : HeapCalls.Env) (xs : List Int) (k : Int)
    (heap : Mutable.Heap) (address : Nat)
    (lookup : env "xs" = some (.ref address)) (bound : env "k" = some (.scalar (.int k)))
    (found : heap[address]? = some (.list (ints xs))) :
    HeapCalls.Evaluates program env (.compare (.builtinCall .len [.name "xs"]) [(.lt, .name "k")])
      heap (.scalar (.bool (decide ((xs.length : Int) < k)))) heap := by
  apply HeapCalls.Evaluates.compare (av := .scalar (.int xs.length)) (middle := heap) (afterRight := heap)
  · exact HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup lookup) .nil)
      (by simp [HeapCalls.primitive, Mutable.length, found, ints])
  · exact HeapCalls.Evaluates.lookup bound
  · simp [HeapCalls.compare, scalarCompare, evalCmpOp]

/-- Recursive window construction only allocates fresh lists. It never modifies caller objects. -/
theorem window_products.result (k : Int) (xs : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (ints xs))) :
    ∃ (finalHeap : Mutable.Heap) (answer : Nat), heap <+: finalHeap ∧
      finalHeap[answer]? = some (.list (ints (windowValues k xs))) ∧
      HeapCalls.ReturnsValue program "window_products" [.scalar (.int k), .ref address] heap (.ref answer) finalHeap := by
  induction xs generalizing heap address with
  | nil =>
      refine ⟨heap ++ [.list []], heap.length, List.prefix_append _ _, ?_, ?_⟩
      · simp [windowValues, ints]
      · apply HeapCalls.BlockReturns.function rfl rfl
        apply HeapCalls.BlockReturns.branch (window.empty_test _ [] heap address rfl found) (flag := true)
        · rfl
        · exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.list .nil)
  | cons head tail ih =>
      by_cases short : (tail.length : Int) + 1 < k
      · refine ⟨heap ++ [.list []], heap.length, List.prefix_append _ _, ?_, ?_⟩
        · simp [windowValues, short, ints]
        · apply HeapCalls.BlockReturns.function rfl rfl
          apply HeapCalls.BlockReturns.branch (window.empty_test _ (head :: tail) heap address rfl found) (flag := false)
          · rfl
          · apply HeapCalls.BlockReturns.branch (window.short_test _ (head :: tail) k heap address rfl rfl found) (flag := true)
            · simp [Mutable.truth, scalarTruth, short]
            · exact HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.list .nil)
      · let selected := (head :: tail).take (FormalSW.Py.Builtin.Slice.prefixLength (head :: tail).length k)
        let product := selected.prod
        let h1 := heap ++ [.list (ints selected)]
        let h2 := h1 ++ [.list [.scalar (.int product)]]
        let h3 := h2 ++ [.list (ints tail)]
        have extends1 : heap <+: h1 := List.prefix_append _ _
        have extends2 : heap <+: h2 := extends1.trans (List.prefix_append _ _)
        have extends3 : heap <+: h3 := extends2.trans (List.prefix_append _ _)
        have prefixFound : h1[heap.length]? = some (.list (ints selected)) := by simp [h1]
        have firstFound : h2[h1.length]? = some (.list [.scalar (.int product)]) := by simp [h2]
        have tailFound : h3[h2.length]? = some (.list (ints tail)) := by simp [h3]
        obtain ⟨last, result, extension, resultFound, recursive⟩ := ih h3 h2.length tailFound
        have firstLast : last[h1.length]? = some (.list [.scalar (.int product)]) :=
          lookup_extended ((List.prefix_append h2 [.list (ints tail)]).trans extension) firstFound
        refine ⟨last ++ [.list (ints (product :: windowValues k tail))], last.length,
          (extends3.trans extension).trans (List.prefix_append _ _), ?_, ?_⟩
        · simp [windowValues, short, product, selected]
        · apply HeapCalls.BlockReturns.function rfl rfl
          apply HeapCalls.BlockReturns.branch (window.empty_test _ (head :: tail) heap address rfl found) (flag := false)
          · rfl
          · apply HeapCalls.BlockReturns.branch (window.short_test _ (head :: tail) k heap address rfl rfl found) (flag := false)
            · simp [Mutable.truth, scalarTruth, short]
            · apply HeapCalls.BlockReturns.return_value
              apply HeapCalls.Evaluates.binary (av := .ref h1.length) (bv := .ref result)
                (middle := h2) (afterRight := last)
              · apply HeapCalls.Evaluates.list
                apply HeapCalls.Evaluates.Arguments.cons (middle := h1)
                · apply HeapCalls.Evaluates.call (values := [.ref heap.length]) (middle := h1)
                  · apply HeapCalls.Evaluates.Arguments.cons (middle := h1)
                    · apply HeapCalls.Evaluates.slice
                        (.cons (HeapCalls.Evaluates.lookup rfl) (.cons HeapCalls.Evaluates.constant
                          (.cons (HeapCalls.Evaluates.lookup rfl) (.cons HeapCalls.Evaluates.constant .nil))))
                      simpa [h1, selected, ints, List.map_take] using Mutable.getSlice_list_prefix heap address (ints (head :: tail)) k found
                    · exact .nil
                  · exact list_product.result selected h1 heap.length prefixFound
                · exact .nil
              · apply HeapCalls.Evaluates.call (values := [.scalar (.int k), .ref h2.length]) (middle := h3)
                · apply HeapCalls.Evaluates.Arguments.cons (HeapCalls.Evaluates.lookup rfl)
                  apply HeapCalls.Evaluates.Arguments.cons
                  · apply HeapCalls.Evaluates.slice
                      (.cons (HeapCalls.Evaluates.lookup rfl) (.cons HeapCalls.Evaluates.constant
                        (.cons HeapCalls.Evaluates.constant (.cons HeapCalls.Evaluates.constant .nil))))
                    simpa [h3, ints] using Mutable.getSlice_list_suffix h2 address (ints (head :: tail)) 1
                      (lookup_extended extends2 found)
                  · exact .nil
                · exact recursive
              · simp [Mutable.binary, show (BinOp.add == BinOp.add) = true from rfl, firstLast, resultFound, Mutable.array, Mutable.allocate, ints, Except.map]

/-- The naive function returns a maximum and leaves all input objects unchanged. -/
theorem naive.result (digits : List Int) (k : Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (ints digits))) :
    ∃ finalHeap : Mutable.Heap, heap <+: finalHeap ∧
      HeapCalls.ReturnsValue program "naive" [.ref address, .scalar (.int k)] heap
        (.scalar (.int ((windowValues k digits).foldl max 0))) finalHeap := by
  obtain ⟨finalHeap, answer, extension, resultFound, evaluated⟩ := window_products.result k digits heap address found
  refine ⟨finalHeap, extension, ?_⟩
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  apply HeapCalls.Evaluates.call (values := [.ref answer]) (middle := finalHeap)
  · apply HeapCalls.Evaluates.Arguments.cons (middle := finalHeap)
    · exact HeapCalls.Evaluates.call
        (.cons (HeapCalls.Evaluates.lookup rfl) (.cons (HeapCalls.Evaluates.lookup rfl) .nil)) evaluated
    · exact .nil
  · exact list_max.result (windowValues k digits) finalHeap answer resultFound

/-- The Python source computes the original mathematical specification on natural inputs. -/
theorem naive.naturals (digits : List Nat) (k : Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (ints (digits.map Int.ofNat)))) :
    ∃ finalHeap : Mutable.Heap, heap <+: finalHeap ∧
      HeapCalls.ReturnsValue program "naive" [.ref address, .scalar (.int k)] heap
        (.scalar (.int (ProjectEulerStatements.P8.naive digits k))) finalHeap := by
  obtain ⟨finalHeap, extension, evaluated⟩ := naive.result (digits.map Int.ofNat) k heap address found
  refine ⟨finalHeap, extension, ?_⟩
  have maximum : ((ProjectEulerStatements.P8.windowProducts k digits).map Int.ofNat).foldl max 0 =
      (ProjectEulerStatements.P8.naive digits k : Int) := by
    simpa [ProjectEulerStatements.P8.naive] using maximum_cast (ProjectEulerStatements.P8.windowProducts k digits) 0
  simpa only [windowValues_cast, maximum] using evaluated

theorem window_products.«Returns» (heap : Mutable.Heap) (k : Int) (xs : Nat)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "window_products" [.scalar (.int k), .ref xs] heap).Returns := by
  obtain ⟨values, found⟩ := Mutable.Value.ints_of_hasType typed
  obtain ⟨_, _, _, _, evaluated⟩ := window_products.result k values heap xs found
  exact evaluated.returns

theorem window_products.«Supported» (heap : Mutable.Heap) (k : Int) (xs : Nat)
    (valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "window_products" [.scalar (.int k), .ref xs] heap).Supported :=
  (window_products.«Returns» heap k xs valid typed).supported

theorem naive.«Returns» (heap : Mutable.Heap) (digits : Nat) (k : Int)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref digits) "list[int]") :
    (HeapCalls.call program "naive" [.ref digits, .scalar (.int k)] heap).Returns := by
  obtain ⟨values, found⟩ := Mutable.Value.ints_of_hasType typed
  obtain ⟨_, _, evaluated⟩ := naive.result values k heap digits found
  exact evaluated.returns

theorem naive.«Supported» (heap : Mutable.Heap) (digits : Nat) (k : Int)
    (valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref digits) "list[int]") :
    (HeapCalls.call program "naive" [.ref digits, .scalar (.int k)] heap).Supported :=
  (naive.«Returns» heap digits k valid typed).supported

theorem list_product.«Returns» (heap : Mutable.Heap) (xs : Nat)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "list_product" [.ref xs] heap).Returns := by
  obtain ⟨values, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (list_product.result values heap xs found).returns

theorem list_product.«Supported» (heap : Mutable.Heap) (xs : Nat)
    (valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "list_product" [.ref xs] heap).Supported :=
  (list_product.«Returns» heap xs valid typed).supported

theorem list_max.«Returns» (heap : Mutable.Heap) (xs : Nat)
    (_valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "list_max" [.ref xs] heap).Returns := by
  obtain ⟨values, found⟩ := Mutable.Value.ints_of_hasType typed
  exact (list_max.result values heap xs found).returns

theorem list_max.«Supported» (heap : Mutable.Heap) (xs : Nat)
    (valid : Mutable.Heap.Valid heap) (typed : Mutable.Value.HasType heap (.ref xs) "list[int]") :
    (HeapCalls.call program "list_max" [.ref xs] heap).Supported :=
  (list_max.«Returns» heap xs valid typed).supported

end data.«project-euler-statements».data.py.project_euler_statements.p8
