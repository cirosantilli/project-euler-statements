import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p37.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.SumCalls
import lang.py.FormalSW.TruthCalls
import ProjectEulerStatements.Lib.TruncatablePrimeDigits
import Mathlib.Data.List.Range

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p37
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.TruncatablePrimeBase
private abbrev program := P37Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (items : List Nat) : List Mutable.Value := items.map number

theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 5 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["truncations", "is_truncatable_prime", "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem found_append {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) (extra : Mutable.Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem digits_be_result (radix n : Nat) (valid : 2 ≤ radix) (heap : Mutable.Heap) :
    ReturnsValue program "digits_be" [number n, number radix] heap (.ref (heap.length + 1))
      (heap ++ [.list (numbers (Nat.digits radix n)), .list (numbers (digitsBE radix n))]) := by
  simpa only [numbers, number, digitsBE, List.map_reverse] using
    (common.digits_be.result n radix valid heap).extend common_extension

private theorem of_digits_be_result (radix : Nat) (items : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue program "of_digits_be" [.ref address, number radix] heap
      (number (ofDigitsBE radix items)) (heap ++ [.list (numbers items.reverse)]) := by
  have executed := common.of_digits_be.result (items.map (fun (n : Nat) => (n : Int))) radix heap address
    (by simpa [numbers, number, List.map_map] using found)
  have naturalValue : ProjectEulerStatements.PositionalDigits.value radix
      ((items.map (fun (n : Nat) => (n : Int))).reverse) =
        ((Nat.ofDigits radix items.reverse : Nat) : Int) := by
    simpa only [List.map_reverse] using
      ProjectEulerStatements.PositionalDigits.value_naturals radix items.reverse
  rw [naturalValue] at executed
  simpa only [numbers, number, ofDigitsBE, List.map_reverse, List.map_map] using
    executed.extend common_extension

private abbrev leftSlice : Expr := .subscript (.name "digits")
  (.slice (some (.binOp (.name "i") .add (.constant (.int 1)))) none none)
private abbrev rightSlice : Expr := .subscript (.name "digits")
  (.slice none (some (.binOp (.binOp (.name "width") .sub (.name "i")) .sub (.constant (.int 1)))) none)
private abbrev partExpr (left : Bool) : Expr :=
  .call (.name "of_digits_be") [if left then leftSlice else rightSlice, .name "base"]
private def partDigits (left : Bool) (items : List Nat) (index : Nat) : List Nat :=
  if left then items.drop (index + 1) else items.take (items.length - index - 1)
private def partValue (radix : Nat) (left : Bool) (items : List Nat) (index : Nat) : Nat :=
  ofDigitsBE radix (partDigits left items index)
private abbrev partHeap (left : Bool) (items : List Nat) (index : Nat) : Mutable.Heap :=
  [.list (numbers (partDigits left items index)), .list (numbers (partDigits left items index).reverse)]

/-- The slice is allocated before positional conversion allocates its reversed copy. -/
private theorem part_result (radix : Nat) (left : Bool) (items : List Nat) (index : Nat)
    (within : index < items.length - 1) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) (env : HeapCalls.Env)
    (getDigits : env "digits" = some (.ref address)) (getLength : env "width" = some (number items.length))
    (getIndex : env "i" = some (number index))
    (getBase : env "base" = some (number radix)) :
    Evaluates program env (partExpr left) heap (number (partValue radix left items index))
      (heap ++ partHeap left items index) := by
  have sliced : Evaluates program env (if left then leftSlice else rightSlice) heap (.ref heap.length)
      (heap ++ [.list (numbers (partDigits left items index))]) := by
    cases left with
    | true =>
        apply Evaluates.slice (.cons (Evaluates.lookup getDigits) (.cons
          (Evaluates.binary (av := number index) (bv := number 1) (value := number (index + 1))
            (middle := heap) (afterRight := heap) (finalHeap := heap)
            (Evaluates.lookup getIndex) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number]))
          (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
        simpa [partDigits, numbers] using Mutable.getSlice_list_suffix heap address (numbers items) (index + 1) found
    | false =>
        apply Evaluates.slice (.cons (Evaluates.lookup getDigits) (.cons Evaluates.constant (.cons
          (Evaluates.binary (av := number (items.length - index)) (bv := number 1)
            (value := number (items.length - index - 1)) (middle := heap) (afterRight := heap) (finalHeap := heap)
            (Evaluates.binary (av := number items.length) (bv := number index)
              (value := number (items.length - index)) (middle := heap) (afterRight := heap) (finalHeap := heap)
              (Evaluates.lookup getLength) (Evaluates.lookup getIndex)
              (by simp [Mutable.binary, scalarBinary, number, Int.natCast_sub (show index ≤ items.length by omega)]))
            Evaluates.constant
            (by simp [Mutable.binary, scalarBinary, number, Int.natCast_sub (show 1 ≤ items.length - index by omega)]))
          (.cons Evaluates.constant .nil))))
        simpa [partDigits, numbers, FormalSW.Py.Builtin.Slice.prefixLength_nonnegative,
          Nat.min_eq_left (show items.length - index - 1 ≤ items.length by omega)] using
          Mutable.getSlice_list_prefix heap address (numbers items) ((items.length - index - 1 : Nat) : Int) found
  have converted := of_digits_be_result radix (partDigits left items index)
    (heap ++ [.list (numbers (partDigits left items index))]) heap.length (by simp)
  have called := Evaluates.call (module := program) (env := env) (.cons sliced (.cons (Evaluates.lookup getBase) .nil)) converted
  simpa only [partExpr, partValue, partHeap, List.append_assoc, List.singleton_append] using called

private def collectorHeap (base : Mutable.Heap) (values : List Nat) (extra : Mutable.Heap) : Mutable.Heap :=
  base ++ [.list (numbers values)] ++ extra
private def partValues (radix : Nat) (left : Bool) (items : List Nat) : List Nat :=
  (List.range (items.length - 1)).map (partValue radix left items)

private theorem collect_parts (radix : Nat) (left : Bool) (items : List Nat) (first count : Nat)
    (bound : first + count = items.length - 1) (base : Mutable.Heap) (address : Nat)
    (found : base[address]? = some (.list (numbers items)))
    (before : List Nat) (extra : Mutable.Heap) (env : HeapCalls.Env)
    (getDigits : env "digits" = some (.ref address)) (getLength : env "width" = some (number items.length))
    (getBase : env "base" = some (number radix)) :
    ∃ finalEnv finalExtra, BlockContinues program env
      [.rangeStepLoop "i" first ((items.length : Int) - 1) 1
        [.comprehensionAppend base.length (partExpr left)] []]
      (collectorHeap base before extra) finalEnv
      (collectorHeap base (before ++ (List.range' first count).map (partValue radix left items)) finalExtra) := by
  induction count generalizing first before extra env with
  | zero =>
      refine ⟨env, extra, ?_⟩
      simpa only [List.range'_zero, List.map_nil, List.append_nil] using
        (BlockContinues.range_done (module := program) (env := env)
          (name := "i") (next := first) (stop := (items.length : Int) - 1) (stride := 1)
          (body := [.comprehensionAppend base.length (partExpr left)]) (otherwise := [])
          (heap := collectorHeap base before extra)
          (by simp [Calls.rangeContinues]; omega) BlockContinues.nil)
  | succ count ih =>
      let boundEnv := setLocal env "i" (number first)
      let heap := collectorHeap base before extra
      let allocated := partHeap left items first
      have inputFound : heap[address]? = some (.list (numbers items)) :=
        found_append (found_append found _) extra
      have collectorFound : heap[base.length]? = some (.list (numbers before)) := by
        simp [heap, collectorHeap, List.append_assoc]
      have element := part_result radix left items first (by omega) heap address inputFound boundEnv
        (by simpa [boundEnv, setLocal] using getDigits)
        (by simpa [boundEnv, setLocal] using getLength) (by simp [boundEnv, setLocal])
        (by simpa [boundEnv, setLocal] using getBase)
      have appended : BlockContinues program boundEnv
          [.comprehensionAppend base.length (partExpr left)] heap boundEnv
          (collectorHeap base (before ++ [partValue radix left items first]) (extra ++ allocated)) := by
        have executed := BlockContinues.comprehension_append element (found_append collectorFound allocated)
        simpa [heap, collectorHeap, numbers, List.map_append, List.append_assoc,
          List.set_append_right] using executed
      obtain ⟨finalEnv, finalExtra, rest⟩ := ih (first + 1) (by omega)
        (before ++ [partValue radix left items first]) (extra ++ allocated) boundEnv
        (by simpa [boundEnv, setLocal] using getDigits) (by simpa [boundEnv, setLocal] using getLength)
        (by simpa [boundEnv, setLocal] using getBase)
      refine ⟨finalEnv, finalExtra, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        List.range'_succ, List.append_assoc, Nat.cast_add, Nat.cast_one] using appended.append rest

private theorem parts_result (radix : Nat) (left : Bool) (items : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) (env : HeapCalls.Env)
    (getDigits : env "digits" = some (.ref address)) (getLength : env "width" = some (number items.length))
    (getBase : env "base" = some (number radix)) :
    ∃ extra, Evaluates program env
      (.listComp (partExpr left)
        [("i", .call (.name "range") [.binOp (.name "width") .sub (.constant (.int 1))], [])])
      heap (.ref heap.length) (collectorHeap heap (partValues radix left items) extra) := by
  let generators : List (String × Expr × List Expr) :=
    [("i", .call (.name "range") [.binOp (.name "width") .sub (.constant (.int 1))], [])]
  obtain ⟨finalEnv, extra, collected⟩ := collect_parts radix left items 0 (items.length - 1) (by omega)
    heap address found [] [] (comprehensionEnv env generators)
    (by simpa [generators, comprehensionEnv] using getDigits)
    (by simpa [generators, comprehensionEnv] using getLength)
    (by simpa [generators, comprehensionEnv] using getBase)
  refine ⟨extra, ?_⟩
  apply Evaluates.list_comp_range (values := [.scalar (.int ((items.length : Int) - 1))])
    (middle := heap) (finalEnv := finalEnv)
    (.cons (Evaluates.binary (av := number items.length) (bv := number 1)
      (value := .scalar (.int ((items.length : Int) - 1))) (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup getLength) Evaluates.constant (by simp [Mutable.binary, scalarBinary])) .nil) rfl
  simpa only [collectorHeap, List.append_nil, List.nil_append, partValues, List.range_eq_range'] using collected

/-- Both eager comprehensions run before concatenation; each conversion keeps its own copies. -/
theorem truncations.result (radix n : Nat) (valid : 2 ≤ radix) (heap : Mutable.Heap) :
    ∃ extra address, ReturnsValue program "truncations" [number n, number radix] heap (.ref address) (heap ++ extra) ∧
      (heap ++ extra)[address]? = some (.list (numbers (truncations radix n))) := by
  let items := digitsBE radix n
  let initial := functionEnv ((findFunctionIn program.body "truncations").getD ([], [])).1
    ((findFunctionIn program.body "truncations").getD ([], [])).2 [number n, number radix] []
  let digitsHeap := heap ++ [.list (numbers (Nat.digits radix n)), .list (numbers items)]
  let withDigits := setLocal initial "digits" (.ref (heap.length + 1))
  let ready := setLocal withDigits "width" (number items.length)
  have found : digitsHeap[heap.length + 1]? = some (.list (numbers items)) := by simp [digitsHeap]
  obtain ⟨leftExtra, left⟩ := parts_result radix true items digitsHeap (heap.length + 1) found ready
    (by simp [ready, withDigits, setLocal]) (by simp [ready, setLocal])
    (by simp [ready, withDigits, initial, setLocal]; rfl)
  let leftHeap := collectorHeap digitsHeap (partValues radix true items) leftExtra
  have leftFound : leftHeap[digitsHeap.length]? = some (.list (numbers (partValues radix true items))) := by
    simp [leftHeap, collectorHeap, List.append_assoc]
  obtain ⟨rightExtra, right⟩ := parts_result radix false items leftHeap (heap.length + 1)
    (found_append (found_append found _) leftExtra) ready
    (by simp [ready, withDigits, setLocal]) (by simp [ready, setLocal])
    (by simp [ready, withDigits, initial, setLocal]; rfl)
  let rightHeap := collectorHeap leftHeap (partValues radix false items) rightExtra
  have leftStill : rightHeap[digitsHeap.length]? = some (.list (numbers (partValues radix true items))) :=
    found_append (found_append leftFound _) rightExtra
  have rightFound : rightHeap[leftHeap.length]? = some (.list (numbers (partValues radix false items))) := by
    simp [rightHeap, collectorHeap, List.append_assoc]
  have values : partValues radix true items ++ partValues radix false items = truncations radix n := by
    simp only [partValues, truncations, items]
    rfl
  have encoded : numbers (partValues radix true items) ++ numbers (partValues radix false items) = numbers (truncations radix n) := by
    change (partValues radix true items).map number ++ (partValues radix false items).map number = (truncations radix n).map number
    rw [← List.map_append, values]
  let allocated : Mutable.Heap :=
    [.list (numbers (Nat.digits radix n)), .list (numbers items), .list (numbers (partValues radix true items))] ++
    leftExtra ++ [.list (numbers (partValues radix false items))] ++ rightExtra ++ [.list (numbers (truncations radix n))]
  have finalHeap : rightHeap ++ [.list (numbers (truncations radix n))] = heap ++ allocated := by
    simp [rightHeap, leftHeap, collectorHeap, digitsHeap, allocated, List.append_assoc]
  refine ⟨allocated, rightHeap.length, ?_, ?_⟩
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil))
      (digits_be_result radix n valid heap))
    apply BlockReturns.assign (value := number items.length) (middle := digitsHeap)
    · apply Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil)
      simp [primitive, Mutable.length, numbers, items, digitsHeap]
    · apply BlockReturns.return_value
      rw [← finalHeap]
      apply Evaluates.binary (av := .ref digitsHeap.length) (bv := .ref leftHeap.length)
        (middle := leftHeap) (afterRight := rightHeap) left right
      dsimp only [Mutable.binary]
      simp only [show (BinOp.add == BinOp.add) = true from rfl, if_true]
      simp [Mutable.array, Mutable.allocate, Except.map, leftStill, rightFound, encoded]
  · rw [← finalHeap]
    simp

end data.«project-euler-statements».data.py.project_euler_statements.p37
