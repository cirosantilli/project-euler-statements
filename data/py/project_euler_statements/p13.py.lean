import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p13.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerStatements.Lib.PositionalDigits
import ProjectEulerStatements.P13

namespace data.«project-euler-statements».data.py.project_euler_statements.p13
open FormalSW.PyAst
private abbrev program := P13Ast.module

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 1 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["naive"] at member
    simp only [List.mem_singleton] at member
    subst name
    decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private abbrev encode (items : List Int) : List Mutable.Value :=
  items.map (fun n => .scalar (.int n))

private abbrev digits (n : Nat) : List Int :=
  (Nat.digits 10 n).map (fun (d : Nat) => (d : Int))

private abbrev selectedDigits (n : Nat) (k : Int) : List Int :=
  (digits n).reverse.take (FormalSW.Py.Builtin.Slice.prefixLength (digits n).length k)

private def finalHeap (heap : Mutable.Heap) (n : Nat) (k : Int) : Mutable.Heap :=
  heap ++ [.list (encode (digits n)), .list (encode (digits n).reverse),
    .list (encode (selectedDigits n k)), .list (encode (selectedDigits n k).reverse)]

private theorem sum.evaluates (env : HeapCalls.Env) (heap : Mutable.Heap) (address : Nat)
    (items : List Int) (found : heap[address]? = some (.list (encode items)))
    (lookup : env "nums" = some (.ref address)) :
    HeapCalls.Evaluates program env (.sumSequence (.name "nums") (.constant (.int 0))) heap
      (.scalar (.int (items.foldl Int.add 0))) heap := by
  apply HeapCalls.Evaluates.sum_integers
    (.cons (HeapCalls.Evaluates.lookup lookup) (.cons HeapCalls.Evaluates.constant .nil))
  simp [Mutable.sequence, found]

/-- Exact evaluation for any signed input list with a nonnegative sum, including negative slice stops. -/
theorem naive.result (heap : Mutable.Heap) (address : Nat) (items : List Int) (k : Int)
    (found : heap[address]? = some (.list (encode items))) (nonnegative : 0 ≤ items.foldl Int.add 0) :
    HeapCalls.ReturnsValue program "naive" [.ref address, .scalar (.int k)] heap
      (.scalar (.int (ProjectEulerStatements.PositionalDigits.value 10
        (selectedDigits (items.foldl Int.add 0).toNat k).reverse)))
      (finalHeap heap (items.foldl Int.add 0).toNat k) := by
  let n := (items.foldl Int.add 0).toNat
  let env := HeapCalls.argumentEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    [.ref address, .scalar (.int k)]
  let firstHeap := heap ++ [.list (encode (digits n)), .list (encode (digits n).reverse)]
  let slicedHeap := firstHeap ++ [.list (encode (selectedDigits n k))]
  have converted : HeapCalls.ReturnsValue program "digits_be" [.scalar (.int (items.foldl Int.add 0))]
      heap (.ref (heap.length + 1)) firstHeap := by
    have called := (common.digits_be.result n 10 (by decide) heap).extend common_extension
    have defaulted := HeapCalls.ReturnsValue.with_defaults (name := "digits_be")
      (supplied := [.scalar (.int n)]) rfl rfl rfl called
    simpa [firstHeap, encode, digits, n, List.map_map, Function.comp_def,
      Int.toNat_of_nonneg nonnegative] using defaulted
  have computed : HeapCalls.Evaluates program env
      (.call (.name "digits_be") [.sumSequence (.name "nums") (.constant (.int 0))])
      heap (.ref (heap.length + 1)) firstHeap :=
    HeapCalls.Evaluates.call (.cons (sum.evaluates env heap address items found rfl) .nil) converted
  have sliced : HeapCalls.Evaluates program env
      (.subscript (.call (.name "digits_be") [.sumSequence (.name "nums") (.constant (.int 0))])
        (.slice none (some (.name "k")) none)) heap (.ref firstHeap.length) slicedHeap := by
    apply HeapCalls.Evaluates.slice (.cons computed (.cons HeapCalls.Evaluates.constant
      (.cons (HeapCalls.Evaluates.lookup rfl) (.cons HeapCalls.Evaluates.constant .nil))))
    simpa [HeapCalls.primitive, slicedHeap, selectedDigits, encode, List.map_take, List.map_reverse] using
      Mutable.getSlice_list_prefix firstHeap (heap.length + 1) (encode (digits n).reverse) k
        (by simp [firstHeap])
  have returned := (common.of_digits_be.result (selectedDigits n k) 10 slicedHeap firstHeap.length
    (by simp [slicedHeap])).extend common_extension
  have defaulted := HeapCalls.ReturnsValue.with_defaults (name := "of_digits_be")
    (supplied := [.ref firstHeap.length]) rfl rfl rfl returned
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.return_value
  simpa [finalHeap, slicedHeap, firstHeap, List.append_assoc, n] using
    HeapCalls.Evaluates.call (.cons sliced .nil) defaulted

/-- On natural inputs the actual Python program computes the existing mathematical specification. -/
theorem naive.natural (heap : Mutable.Heap) (address : Nat) (nums : List Nat) (k : Nat)
    (found : heap[address]? = some (.list (encode (nums.map (fun (n : Nat) => (n : Int)))))) :
    HeapCalls.ReturnsValue program "naive" [.ref address, .scalar (.int k)] heap
      (.scalar (.int (ProjectEulerStatements.P13.naive nums k))) (finalHeap heap nums.sum k) := by
  have summed : (nums.map (fun (n : Nat) => (n : Int))).foldl Int.add 0 = (nums.sum : Int) := by
    calc
      _ = (nums.map (fun (n : Nat) => (n : Int))).sum := List.sum_eq_foldl.symm
      _ = _ := by simp
  have selected : selectedDigits nums.sum k =
      ((Nat.digits 10 nums.sum).reverse.take k).map (fun (n : Nat) => (n : Int)) := by
    rw [List.take_eq_take_min (l := (Nat.digits 10 nums.sum).reverse) (i := k)]
    simp [selectedDigits, digits, FormalSW.Py.Builtin.Slice.prefixLength_nonnegative,
      List.map_reverse, List.map_take]
  have executed := naive.result heap address (nums.map (fun (n : Nat) => (n : Int))) k found
    (by rw [summed]; omega)
  have resultValue : ProjectEulerStatements.PositionalDigits.value 10 (selectedDigits nums.sum k).reverse =
      (ProjectEulerStatements.P13.naive nums k : Int) := by
    rw [selected, ← List.map_reverse]
    exact ProjectEulerStatements.PositionalDigits.value_naturals 10 _
  simpa only [summed, Int.toNat_natCast, resultValue] using executed

/-- Signed inputs with the same nonnegative sum have the same leading-digit result. -/
theorem naive.sum_result (heap : Mutable.Heap) (address : Nat) (items : List Int) (n k : Nat)
    (found : heap[address]? = some (.list (encode items))) (summed : items.foldl Int.add 0 = (n : Int)) :
    ∃ extra, HeapCalls.ReturnsValue program "naive" [.ref address, .scalar (.int k)] heap
      (.scalar (.int (ProjectEulerStatements.P13.naive [n] k))) (heap ++ extra) := by
  have selected : selectedDigits n k =
      ((Nat.digits 10 n).reverse.take k).map (fun (d : Nat) => (d : Int)) := by
    rw [List.take_eq_take_min (l := (Nat.digits 10 n).reverse) (i := k)]
    simp [selectedDigits, digits, FormalSW.Py.Builtin.Slice.prefixLength_nonnegative,
      List.map_reverse, List.map_take]
  have resultValue : ProjectEulerStatements.PositionalDigits.value 10 (selectedDigits n k).reverse =
      (ProjectEulerStatements.P13.naive [n] k : Int) := by
    rw [selected, ← List.map_reverse]
    exact ProjectEulerStatements.PositionalDigits.value_naturals 10 _
  have executed := naive.result heap address items k found (by rw [summed]; omega)
  refine ⟨finalHeap [] n k, ?_⟩
  simpa only [summed, Int.toNat_natCast, resultValue] using executed

private theorem prerequisite (heap : Mutable.Heap) (address : Nat) (items : List Int)
    (found : heap[address]? = some (.list (encode items))) :
    HeapCalls.Evaluates program (fun name => if name = "nums" then some (.ref address) else none)
      P13Ast.requires_naive_0 heap (.scalar (.bool (decide (0 ≤ items.foldl Int.add 0)))) heap := by
  apply HeapCalls.Evaluates.compare
    (sum.evaluates _ heap address items found rfl) HeapCalls.Evaluates.constant
  simp [HeapCalls.compare, scalarCompare, evalCmpOp]

theorem requires_naive_0_supported (heap : Mutable.Heap) (address : Nat) (_k : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.evaluate program (fun name => if name = "nums" then some (.ref address) else none)
      P13Ast.requires_naive_0 heap).Supported := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  exact Execution.supported_of_finishes (prerequisite heap address items found).finishes

theorem naive.«Returns» (heap : Mutable.Heap) (address : Nat) (k : Int)
    (_valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (requires : HeapCalls.Condition program (fun name => if name = "nums" then some (.ref address) else none)
      P13Ast.requires_naive_0 heap) :
    (HeapCalls.call program "naive" [.ref address, .scalar (.int k)] heap).Returns := by
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  have nonnegative : 0 ≤ items.foldl Int.add 0 := by
    simpa using (prerequisite heap address items found).condition_iff.mp requires
  exact (naive.result heap address items k found nonnegative).returns

theorem naive.«Supported» (heap : Mutable.Heap) (address : Nat) (k : Int)
    (valid : heap.Valid) (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (requires : HeapCalls.Condition program (fun name => if name = "nums" then some (.ref address) else none)
      P13Ast.requires_naive_0 heap) :
    (HeapCalls.call program "naive" [.ref address, .scalar (.int k)] heap).Supported :=
  (naive.«Returns» heap address k valid typed requires).supported

end data.«project-euler-statements».data.py.project_euler_statements.p13
