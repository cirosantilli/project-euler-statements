import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p37.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.SumCalls
import lang.py.FormalSW.TruthCalls
import ProjectEulerStatements.Lib.TruncatablePrimes
import Mathlib.Data.List.Range

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p37
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.P37
private abbrev program := P37Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (items : List Nat) : List Mutable.Value := items.map number

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
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

private theorem digits_be_result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "digits_be" [number n] heap (.ref (heap.length + 1))
      (heap ++ [.list (numbers (Nat.digits 10 n)), .list (numbers (digitsBE n))]) := by
  have executed := common.digits_be.result n 10 (by omega) heap
  have defaulted := ReturnsValue.with_defaults (supplied := [number n]) rfl rfl rfl executed
  simpa only [numbers, number, digitsBE, List.map_reverse] using defaulted.extend common_extension

private theorem of_digits_be_result (items : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue program "of_digits_be" [.ref address] heap (number (digitsToNat items))
      (heap ++ [.list (numbers items.reverse)]) := by
  have executed := common.of_digits_be.result (items.map (fun (n : Nat) => (n : Int))) 10 heap address
    (by simpa [numbers, number, List.map_map] using found)
  have naturalValue : ProjectEulerStatements.PositionalDigits.value 10
      ((items.map (fun (n : Nat) => (n : Int))).reverse) = ((Nat.ofDigits 10 items.reverse : Nat) : Int) := by
    simpa only [Nat.cast_ofNat, List.map_reverse] using
      ProjectEulerStatements.PositionalDigits.value_naturals 10 items.reverse
  rw [naturalValue] at executed
  have defaulted := ReturnsValue.with_defaults (supplied := [.ref address]) rfl rfl rfl executed
  simpa only [numbers, number, digitsToNat, List.map_reverse, List.map_map] using defaulted.extend common_extension

private abbrev leftSlice : Expr := .subscript (.name "ds")
  (.slice (some (.binOp (.name "i") .add (.constant (.int 1)))) none none)
private abbrev rightSlice : Expr := .subscript (.name "ds")
  (.slice none (some (.binOp (.binOp (.name "l") .sub (.name "i")) .sub (.constant (.int 1)))) none)
private abbrev partExpr (left : Bool) : Expr :=
  .call (.name "of_digits_be") [if left then leftSlice else rightSlice]
private def partDigits (left : Bool) (items : List Nat) (index : Nat) : List Nat :=
  if left then items.drop (index + 1) else items.take (items.length - index - 1)
private def partValue (left : Bool) (items : List Nat) (index : Nat) : Nat :=
  digitsToNat (partDigits left items index)
private abbrev partHeap (left : Bool) (items : List Nat) (index : Nat) : Mutable.Heap :=
  [.list (numbers (partDigits left items index)), .list (numbers (partDigits left items index).reverse)]

/-- The slice is allocated before positional conversion allocates its reversed copy. -/
private theorem part_result (left : Bool) (items : List Nat) (index : Nat)
    (within : index < items.length - 1) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) (env : HeapCalls.Env)
    (getDigits : env "ds" = some (.ref address)) (getLength : env "l" = some (number items.length))
    (getIndex : env "i" = some (number index)) :
    Evaluates program env (partExpr left) heap (number (partValue left items index))
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
  have converted := of_digits_be_result (partDigits left items index)
    (heap ++ [.list (numbers (partDigits left items index))]) heap.length (by simp)
  have called := Evaluates.call (module := program) (env := env) (.cons sliced .nil) converted
  simpa only [partExpr, partValue, partHeap, List.append_assoc, List.singleton_append] using called

private def collectorHeap (base : Mutable.Heap) (values : List Nat) (extra : Mutable.Heap) : Mutable.Heap :=
  base ++ [.list (numbers values)] ++ extra
private def partValues (left : Bool) (items : List Nat) : List Nat :=
  (List.range (items.length - 1)).map (partValue left items)

private theorem collect_parts (left : Bool) (items : List Nat) (first count : Nat)
    (bound : first + count = items.length - 1) (base : Mutable.Heap) (address : Nat)
    (found : base[address]? = some (.list (numbers items)))
    (before : List Nat) (extra : Mutable.Heap) (env : HeapCalls.Env)
    (getDigits : env "ds" = some (.ref address)) (getLength : env "l" = some (number items.length)) :
    ∃ finalEnv finalExtra, BlockContinues program env
      [.rangeStepLoop "i" first ((items.length : Int) - 1) 1
        [.comprehensionAppend base.length (partExpr left)] []]
      (collectorHeap base before extra) finalEnv
      (collectorHeap base (before ++ (List.range' first count).map (partValue left items)) finalExtra) := by
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
      have element := part_result left items first (by omega) heap address inputFound boundEnv
        (by simpa [boundEnv, setLocal] using getDigits)
        (by simpa [boundEnv, setLocal] using getLength) (by simp [boundEnv, setLocal])
      have appended : BlockContinues program boundEnv
          [.comprehensionAppend base.length (partExpr left)] heap boundEnv
          (collectorHeap base (before ++ [partValue left items first]) (extra ++ allocated)) := by
        have executed := BlockContinues.comprehension_append element (found_append collectorFound allocated)
        simpa [heap, collectorHeap, numbers, List.map_append, List.append_assoc,
          List.set_append_right] using executed
      obtain ⟨finalEnv, finalExtra, rest⟩ := ih (first + 1) (by omega)
        (before ++ [partValue left items first]) (extra ++ allocated) boundEnv
        (by simpa [boundEnv, setLocal] using getDigits) (by simpa [boundEnv, setLocal] using getLength)
      refine ⟨finalEnv, finalExtra, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        List.range'_succ, List.append_assoc, Nat.cast_add, Nat.cast_one] using appended.append rest

private theorem parts_result (left : Bool) (items : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) (env : HeapCalls.Env)
    (getDigits : env "ds" = some (.ref address)) (getLength : env "l" = some (number items.length)) :
    ∃ extra, Evaluates program env
      (.listComp (partExpr left)
        [("i", .call (.name "range") [.binOp (.name "l") .sub (.constant (.int 1))], [])])
      heap (.ref heap.length) (collectorHeap heap (partValues left items) extra) := by
  let generators : List (String × Expr × List Expr) :=
    [("i", .call (.name "range") [.binOp (.name "l") .sub (.constant (.int 1))], [])]
  obtain ⟨finalEnv, extra, collected⟩ := collect_parts left items 0 (items.length - 1) (by omega)
    heap address found [] [] (comprehensionEnv env generators)
    (by simpa [generators, comprehensionEnv] using getDigits)
    (by simpa [generators, comprehensionEnv] using getLength)
  refine ⟨extra, ?_⟩
  apply Evaluates.list_comp_range (values := [.scalar (.int ((items.length : Int) - 1))])
    (middle := heap) (finalEnv := finalEnv)
    (.cons (Evaluates.binary (av := number items.length) (bv := number 1)
      (value := .scalar (.int ((items.length : Int) - 1))) (middle := heap) (afterRight := heap) (finalHeap := heap)
      (Evaluates.lookup getLength) Evaluates.constant (by simp [Mutable.binary, scalarBinary])) .nil) rfl
  simpa only [collectorHeap, List.append_nil, List.nil_append, partValues, List.range_eq_range'] using collected

/-- Both eager comprehensions run before concatenation; each conversion keeps its own copies. -/
theorem truncations.result (n : Nat) (heap : Mutable.Heap) :
    ∃ extra address, ReturnsValue program "truncations" [number n] heap (.ref address) (heap ++ extra) ∧
      (heap ++ extra)[address]? = some (.list (numbers (truncations n))) := by
  let items := digitsBE n
  let initial := functionEnv ((findFunctionIn program.body "truncations").getD ([], [])).1
    ((findFunctionIn program.body "truncations").getD ([], [])).2 [number n] []
  let digitsHeap := heap ++ [.list (numbers (Nat.digits 10 n)), .list (numbers items)]
  let withDigits := setLocal initial "ds" (.ref (heap.length + 1))
  let ready := setLocal withDigits "l" (number items.length)
  have found : digitsHeap[heap.length + 1]? = some (.list (numbers items)) := by simp [digitsHeap]
  obtain ⟨leftExtra, left⟩ := parts_result true items digitsHeap (heap.length + 1) found ready
    (by simp [ready, withDigits, setLocal]) (by simp [ready, setLocal])
  let leftHeap := collectorHeap digitsHeap (partValues true items) leftExtra
  have leftFound : leftHeap[digitsHeap.length]? = some (.list (numbers (partValues true items))) := by
    simp [leftHeap, collectorHeap, List.append_assoc]
  obtain ⟨rightExtra, right⟩ := parts_result false items leftHeap (heap.length + 1)
    (found_append (found_append found _) leftExtra) ready
    (by simp [ready, withDigits, setLocal]) (by simp [ready, setLocal])
  let rightHeap := collectorHeap leftHeap (partValues false items) rightExtra
  have leftStill : rightHeap[digitsHeap.length]? = some (.list (numbers (partValues true items))) :=
    found_append (found_append leftFound _) rightExtra
  have rightFound : rightHeap[leftHeap.length]? = some (.list (numbers (partValues false items))) := by
    simp [rightHeap, collectorHeap, List.append_assoc]
  have values : partValues true items ++ partValues false items = truncations n := by
    simp only [partValues, truncations, items]
    rfl
  have encoded : numbers (partValues true items) ++ numbers (partValues false items) = numbers (truncations n) := by
    change (partValues true items).map number ++ (partValues false items).map number = (truncations n).map number
    rw [← List.map_append, values]
  let allocated : Mutable.Heap :=
    [.list (numbers (Nat.digits 10 n)), .list (numbers items), .list (numbers (partValues true items))] ++
    leftExtra ++ [.list (numbers (partValues false items))] ++ rightExtra ++ [.list (numbers (truncations n))]
  have finalHeap : rightHeap ++ [.list (numbers (truncations n))] = heap ++ allocated := by
    simp [rightHeap, leftHeap, collectorHeap, digitsHeap, allocated, List.append_assoc]
  refine ⟨allocated, rightHeap.length, ?_, ?_⟩
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (digits_be_result n heap))
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

private abbrev allExpr : Expr := .consumeGenerator (.builtinCall .all [])
  (.call (.name "is_prime") [.name "x"])
  [(.name "x", .call (.name "truncations") [.name "n"], [])]

/-- The complete truncation list is built before `all` consumes it lazily. -/
private theorem all_result (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) :
    ∃ extra, Evaluates program env allExpr heap
      (.scalar (.bool ((truncations n).all isPrime))) (heap ++ extra) := by
  obtain ⟨extra, address, truncated, found⟩ := truncations.result n heap
  refine ⟨extra, ?_⟩
  apply Evaluates.all_map (values := truncations n) (encode := number) (predicate := isPrime)
    (by intro expressions; simp) (by intro expressions; simp) (by intro expressions; simp)
    (Evaluates.call (.cons (Evaluates.lookup getN) .nil) truncated)
    (by simp [Mutable.sequence, found, numbers])
  intro inner item selected
  exact Evaluates.call (.cons (Evaluates.lookup selected) .nil)
    ((common.is_prime.heap_result item (heap ++ extra)).extend common_extension)

/-- Threshold and primality guards precede every truncation allocation. -/
theorem is_truncatable_prime.result (n : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "is_truncatable_prime" [number n] heap
      (.scalar (.bool (isTruncatablePrime n))) (heap ++ extra) := by
  let args := ((findFunctionIn program.body "is_truncatable_prime").getD ([], [])).1
  let code := ((findFunctionIn program.body "is_truncatable_prime").getD ([], [])).2
  let env := functionEnv args code [number n] []
  have threshold : Evaluates program env (.compare (.name "n") [(.gt, .constant (.int 7))]) heap
      (.scalar (.bool (decide (7 < n)))) heap :=
    Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  by_cases small : n ≤ 7
  · refine ⟨[], ?_⟩
    simp only [List.append_nil]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    simp only [isTruncatablePrime, if_pos small]
    exact Evaluates.boolean_stop (flag := false)
      (by simpa only [show ¬7 < n by omega, decide_false] using threshold) rfl rfl
  · have primality : Evaluates program env (.call (.name "is_prime") [.name "n"]) heap
        (.scalar (.bool (isPrime n))) heap :=
      Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
        ((common.is_prime.heap_result n heap).extend common_extension)
    by_cases prime : Nat.Prime n
    · obtain ⟨extra, truncated⟩ := all_result n heap env rfl
      refine ⟨extra, ?_⟩
      apply BlockReturns.function rfl rfl
      apply BlockReturns.return_value
      simp only [isTruncatablePrime, if_neg small, isPrime, prime, decide_true, Bool.true_and,
        ProjectEulerStatements.TruncatablePrimes.listAll_map_eq_all]
      apply Evaluates.boolean_next (flag := true)
        (by simpa only [show 7 < n by omega, decide_true] using threshold) rfl rfl
      apply Evaluates.boolean_next (flag := true)
        (by simpa only [isPrime, prime, decide_true] using primality) rfl rfl
      exact Evaluates.boolean_last truncated rfl
    · refine ⟨[], ?_⟩
      simp only [List.append_nil]
      apply BlockReturns.function rfl rfl
      apply BlockReturns.return_value
      simp only [isTruncatablePrime, if_neg small, isPrime, prime, decide_false, Bool.false_and]
      apply Evaluates.boolean_next (flag := true)
        (by simpa only [show 7 < n by omega, decide_true] using threshold) rfl rfl
      exact Evaluates.boolean_stop (flag := false)
        (by simpa only [isPrime, prime, decide_false] using primality) rfl rfl

private abbrev test : Expr := .call (.name "is_truncatable_prime") [.name "n"]
private abbrev body : List Stmt := comprehensionFilters [test] (sumBody (.name "n") [])
private def totalFrom (first count total : Nat) : Nat :=
  (List.range' first count).foldl
    (fun acc n => if ProjectEulerStatements.P37.isTruncatablePrime n then acc + n else acc) total

/-- Every tested value is visited in ascending order; all allocations extend the heap. -/
private theorem naive.loop (count first total : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getTotal : env sumAccumulator = some (number total)) :
    ∃ extra, BlockReturns program env
      [.rangeStepLoop "n" first (first + count) 1 body [], .return (.name sumAccumulator)]
      heap (number (totalFrom first count total)) (heap ++ extra) := by
  induction count generalizing first total heap env with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues])
      exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let boundEnv := setLocal env "n" (number first)
      obtain ⟨allocated, predicate⟩ := is_truncatable_prime.result first heap
      have tested : Evaluates program boundEnv test heap
          (.scalar (.bool (ProjectEulerStatements.P37.isTruncatablePrime first))) (heap ++ allocated) :=
        Evaluates.call (.cons (Evaluates.lookup (by simp [boundEnv, setLocal])) .nil) predicate
      cases yes : ProjectEulerStatements.P37.isTruncatablePrime first with
      | true =>
          let nextEnv := setLocal boundEnv sumAccumulator (number (total + first))
          obtain ⟨rest, continued⟩ := ih (first + 1) (total + first) (heap ++ allocated) nextEnv
            (by simp [nextEnv, setLocal])
          refine ⟨allocated ++ rest, ?_⟩
          apply BlockReturns.range_step (by simp [Calls.rangeContinues])
          apply BlockReturns.branch (flag := true) (by simpa only [yes] using tested) rfl
          apply BlockReturns.assign (value := number (total + first)) (middle := heap ++ allocated)
          · apply Evaluates.binary (av := number total) (bv := number first)
              (Evaluates.lookup (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal))
              (Evaluates.lookup (by simp [setLocal]))
            simp [Mutable.binary, scalarBinary, number]
          · simpa [body, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
              Calls.loopControlStmt, totalFrom, List.range'_succ, List.foldl_cons, yes, nextEnv, boundEnv,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm,
              List.append_assoc] using continued
      | false =>
          obtain ⟨rest, continued⟩ := ih (first + 1) total (heap ++ allocated) boundEnv
            (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal)
          refine ⟨allocated ++ rest, ?_⟩
          apply BlockReturns.range_step (by simp [Calls.rangeContinues])
          apply BlockReturns.branch (flag := false) (by simpa only [yes] using tested) rfl
          simpa [body, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt, totalFrom, List.range'_succ, List.foldl_cons, yes, boundEnv,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm,
            List.append_assoc] using continued

private theorem totalFrom_naive (limit : Nat) :
    totalFrom 0 limit 0 = ProjectEulerStatements.P37.naive limit := by
  rw [ProjectEulerStatements.TruncatablePrimes.naive_fold]
  simp only [totalFrom, List.range_eq_range']

theorem naive.result (limit : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive" [number limit] heap
      (number (ProjectEulerStatements.P37.naive limit)) (heap ++ extra) := by
  let env := functionEnv [⟨"limit", some (.name "int"), none⟩]
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit] []
  let summed := setLocal (comprehensionEnv env
    [("n", .call (.name "range") [.name "limit"], [test])]) sumAccumulator (number 0)
  obtain ⟨extra, loop⟩ := naive.loop limit 0 0 heap summed rfl
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range (values := [number limit]) (middle := heap)
    (.cons (Evaluates.lookup rfl) .nil) rfl Evaluates.constant rfl
  simpa only [Nat.zero_add, Nat.cast_zero, Int.zero_add, totalFrom_naive] using loop

theorem naive.«Returns» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P37Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Returns := by
  have nonnegative : 0 ≤ limit := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift limit to Nat using nonnegative
  obtain ⟨_, returned⟩ := naive.result limit []
  exact returned.scalar_returns

theorem naive.«Supported» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P37Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Supported :=
  (naive.«Returns» limit condition).supported


theorem naive_default.result (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "naive_default" [] heap (number (ProjectEulerStatements.P37.naive 1000000))
      (heap ++ extra) := by
  obtain ⟨extra, returned⟩ := naive.result 1000000 heap
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value (Evaluates.call (.cons Evaluates.constant .nil) returned)

theorem naive_default.«Returns» : (HeapCalls.scalarFunction program "naive_default" []).Returns := by
  obtain ⟨_, returned⟩ := naive_default.result []
  exact ReturnsValue.scalar_returns (values := []) returned

theorem naive_default.«Supported» : (HeapCalls.scalarFunction program "naive_default" []).Supported :=
  naive_default.«Returns».supported

end data.«project-euler-statements».data.py.project_euler_statements.p37
