import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p24.py.ast»
import lang.py.FormalSW.PermutationCalls
import lang.py.FormalSW.HeapSortingCalls
import Mathlib.Data.List.Forall2

namespace data.«project-euler-statements».data.py.project_euler_statements.p24
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
private abbrev program := P24Ast.module
private def ints (items : List Int) : List Mutable.Value := items.map fun n => .scalar (.int n)

private theorem inside {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) : address < heap.length := by
  by_cases valid : address < heap.length
  · exact valid
  · rw [List.getElem?_eq_none (by omega)] at found
    cases found

private theorem found_append {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) (tail : Mutable.Heap) :
    (heap ++ tail)[address]? = some object := by
  rw [List.getElem?_append_left (inside found)]
  exact found

private def Preserves (before after : Mutable.Heap) (collector : Nat) : Prop :=
  ∀ address object, address ≠ collector → before[address]? = some object → after[address]? = some object

private theorem Preserves.trans (first : Preserves before middle collector)
    (second : Preserves middle after collector) : Preserves before after collector :=
  fun address object other found => second address object other (first address object other found)

private theorem appended (heap tail : Mutable.Heap) (collector : Nat) : Preserves heap (heap ++ tail) collector :=
  fun _ _ _ found => found_append found tail

private theorem updated (heap : Mutable.Heap) (collector : Nat) (object : Mutable.Object) :
    Preserves heap (heap.set collector object) collector := by
  intro address item other found
  simpa [List.getElem?_set_ne other.symm] using found

/-- Rows have fresh identities after the private collector, and exact contents. -/
private def Rows (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat) (values : List (List Int)) : Prop :=
  List.Forall₂ (fun address row => collector < address ∧ heap[address]? = some (.list (ints row))) addresses values

private theorem Rows.preserve (rows : Rows before collector addresses values)
    (preserved : Preserves before after collector) : Rows after collector addresses values := by
  induction rows with
  | nil => exact .nil
  | @cons address row addresses values head tail ih =>
      exact .cons ⟨head.1, preserved address _ (by omega) head.2⟩ ih

private theorem Rows.find (rows : Rows heap collector addresses values) (member : address ∈ addresses) :
    ∃ row, collector < address ∧ heap[address]? = some (.list (ints row)) := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, head⟩
      · exact ih member

private theorem int_type {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (.list (ints row))) : Mutable.Value.HasType heap (.ref address) "list[int]" := by
  refine ⟨ints row, found, Or.inr ⟨"int", rfl, ?_⟩⟩
  intro item member
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp member
  rfl

private theorem Rows.typed (rows : Rows heap collector addresses values) :
    ∀ address ∈ addresses, Mutable.Value.HasType heap (.ref address) "list[int]" := by
  intro address member
  obtain ⟨row, _, found⟩ := rows.find member
  exact int_type found

private theorem tuple_allocated (heap : Mutable.Heap) (items : List Mutable.Value) :
    ∃ address tail, Mutable.allocateTuple items heap = some (.ok (.ref address), heap ++ tail) ∧
      (heap ++ tail)[address]? = some (.tuple items) := by
  cases items with
  | nil =>
      cases found : heap.findIdx? (fun object => decide (object = .tuple [])) with
      | none =>
          exact ⟨heap.length, [.tuple []], by simp [Mutable.allocateTuple, found, Except.map], by simp⟩
      | some address =>
          obtain ⟨bound, equal, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
          have equal : heap[address] = .tuple [] := of_decide_eq_true equal
          exact ⟨address, [], by simp [Mutable.allocateTuple, found], by simp [List.getElem?_eq_getElem bound, equal]⟩
  | cons head tail =>
      exact ⟨heap.length, [.tuple (head :: tail)], by simp [Mutable.allocateTuple, Except.map], by simp⟩

private abbrev emit (collector : Nat) : List Stmt :=
  [.comprehensionAppend collector (.builtinCall .list [.name "p"])]

private theorem collect_loop (remaining before : List (List Int)) (heap : Mutable.Heap)
    (collector : Nat) (addresses : List Nat) (env : HeapCalls.Env)
    (found : heap[collector]? = some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses before) :
    ∃ finalHeap finalEnv finalAddresses,
      BlockContinues program env
        [.permutationStepLoop "p" (remaining.map fun row => (ints row).map sequenceSource) (emit collector) []]
        heap finalEnv finalHeap ∧
      finalHeap[collector]? = some (.list (finalAddresses.map Mutable.Value.ref)) ∧
      Rows finalHeap collector finalAddresses (before ++ remaining) ∧ Preserves heap finalHeap collector := by
  induction remaining generalizing before heap addresses env with
  | nil =>
      refine ⟨heap, env, addresses, BlockContinues.permutation_done .nil, found, ?_, ?_⟩
      · simpa using rows
      · exact fun _ _ _ h => h
  | cons row remaining ih =>
      obtain ⟨tuple, extra, allocated, tupleFound⟩ := tuple_allocated heap (ints row)
      let middle : Mutable.Heap := heap ++ extra
      let nextAddresses := addresses ++ [middle.length]
      let nextHeap : Mutable.Heap := (middle ++ [Mutable.Object.list (ints row)]).set collector
        (.list (nextAddresses.map Mutable.Value.ref))
      let bound := setLocal env "p" (.ref tuple)
      have collectorBound : collector < middle.length := by
        have bound := inside found
        simp only [middle, List.length_append]
        omega
      have emitted : BlockContinues program bound (emit collector) middle bound nextHeap := by
        have copied := Evaluates.builtin (globals := []) (module := program) (env := bound)
          (.cons (Evaluates.lookup (name := "p") rfl) .nil)
          (primitive_list_tuple middle tuple (ints row) tupleFound)
        have pushed := BlockContinues.comprehension_append (address := collector) copied
          (found_append (found_append found extra) [.list (ints row)])
        simpa [nextHeap, nextAddresses, emit] using pushed
      have nextFound : nextHeap[collector]? = some (.list (nextAddresses.map Mutable.Value.ref)) := by
        apply List.getElem?_set_self
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have preserved : Preserves heap nextHeap collector :=
        (appended heap extra collector).trans
          ((appended middle [.list (ints row)] collector).trans
            (updated (middle ++ [.list (ints row)]) collector (.list (nextAddresses.map Mutable.Value.ref))))
      have fresh : collector < middle.length ∧ nextHeap[middle.length]? = some (.list (ints row)) := by
        refine ⟨collectorBound, ?_⟩
        change ((middle ++ [Mutable.Object.list (ints row)]).set collector _)[middle.length]? = _
        rw [List.getElem?_set_ne (by omega : collector ≠ middle.length)]
        simp
      have nextRows : Rows nextHeap collector nextAddresses (before ++ [row]) :=
        List.rel_append (rows.preserve preserved) (.cons fresh .nil)
      obtain ⟨finalHeap, finalEnv, finalAddresses, executed, finalFound, finalRows, saved⟩ :=
        ih (before ++ [row]) nextHeap nextAddresses bound nextFound nextRows
      refine ⟨finalHeap, finalEnv, finalAddresses, ?_, finalFound, ?_, preserved.trans saved⟩
      · apply BlockContinues.permutation_step (tuple := .ref tuple) (middle := middle)
          (by simpa [List.map_map, Function.comp_def] using allocated)
        simpa [emit, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, bound] using
          emitted.append executed
      · simpa [List.append_assoc] using finalRows

private abbrev generators : List (Expr × Expr × List Expr) :=
  [(.name "p", .permutationsIterable [.name "digits", .constant .none], [])]

private abbrev sortedExpression :=
  Expr.consumeGenerator (.builtinCall .sorted []) (.builtinCall .list [.name "p"]) generators

private def ordered (heap : Mutable.Heap) (addresses : List Nat) : List Mutable.Value :=
  HeapSort.sortBy (fun a b => HeapSort.lexInt (HeapSort.readInts heap a) (HeapSort.readInts heap b))
    (addresses.map Mutable.Value.ref)

private theorem read_ints {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (.list (ints digits))) : HeapSort.readInts heap (.ref address) = digits := by
  simp [HeapSort.readInts, found, ints, List.filterMap_map]

private theorem Rows.project (rows : Rows heap collector addresses values) :
    (addresses.map Mutable.Value.ref).map (HeapSort.readInts heap) = values := by
  induction rows with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, read_ints head.2, ih]

private theorem ordered_project (rows : Rows heap collector addresses values) :
    (ordered heap addresses).map (HeapSort.readInts heap) = HeapSort.sortBy HeapSort.lexInt values := by
  rw [ordered, HeapSort.sortBy_map, rows.project]

/-- Select a one-based Python index, returning an empty row outside the valid range. -/
def selectRow (rows : List (List Int)) (index : Int) : List Int :=
  if 0 ≤ index - 1 ∧ index - 1 < rows.length then rows[(index - 1).toNat]?.getD [] else []

/-- The reference's result expressed entirely as a finite mathematical list. -/
def reference (digits : List Int) (index : Int) : List Int :=
  selectRow (HeapSort.sortBy HeapSort.lexInt (Permutations.rows digits.length digits)) index

private theorem sorted_expression (heap : Mutable.Heap) (address : Nat) (digits : List Int)
    (env : HeapCalls.Env) (lookup : env "digits" = some (.ref address))
    (found : heap[address]? = some (.list (ints digits))) :
    ∃ collectedHeap addresses,
      Evaluates program env sortedExpression heap (.ref collectedHeap.length)
        (collectedHeap ++ [.list (ordered collectedHeap addresses)]) ∧
      Rows collectedHeap heap.length addresses (Permutations.rows digits.length digits) ∧
      Preserves heap collectedHeap heap.length := by
  obtain ⟨middle, finalEnv, addresses, collected, collection, rows, saved⟩ :=
    collect_loop (Permutations.rows digits.length digits) [] (heap ++ [.list []]) heap.length []
      (comprehensionTargetsEnv env generators) (by simp) .nil
  have rows : Rows middle heap.length addresses (Permutations.rows digits.length digits) := by simpa using rows
  refine ⟨middle, addresses, ?_, rows, (appended heap [.list []] heap.length).trans saved⟩
  apply Evaluates.consume_generator_sorted
  apply GeneratorCollects.permutations
    (.cons (Evaluates.lookup lookup) (.cons Evaluates.constant .nil))
    (rows := (Permutations.rows digits.length digits).map fun row => (ints row).map sequenceSource)
    (finalEnv := finalEnv) (collectedHeap := middle)
  · simpa [ints, Permutations.rows_map, List.map_map, Function.comp_def] using
      permutationRows_list heap address (ints digits) found
  · exact collected
  · exact primitive_sorted_values middle heap.length _ _ collection (HeapSort.sort_int_lists middle addresses rows.typed)

private abbrev rankExpression := Expr.binOp (.name "idx") .sub (.constant (.int 1))
private abbrev boundsExpression := Expr.compare (.constant (.int 0))
  [(.ltE, rankExpression), (.lt, .builtinCall .len [.name "ps"])]
private abbrev answerExpression := Expr.ifExp boundsExpression (.subscript (.name "ps") rankExpression) (.list [])

private theorem rank_evaluates (heap : Mutable.Heap) (env : HeapCalls.Env) (index : Int)
    (lookup : env "idx" = some (.scalar (.int index))) :
    Evaluates program env rankExpression heap (.scalar (.int (index - 1))) heap :=
  Evaluates.binary (Evaluates.lookup lookup) Evaluates.constant rfl

private theorem bounds_evaluates (heap : Mutable.Heap) (env : HeapCalls.Env) (index : Int)
    (address : Nat) (items : List Mutable.Value)
    (getIndex : env "idx" = some (.scalar (.int index))) (getRows : env "ps" = some (.ref address))
    (found : heap[address]? = some (.list items)) :
    Evaluates program env boundsExpression heap
      (.scalar (.bool (decide (0 ≤ index - 1 ∧ index - 1 < items.length)))) heap := by
  apply Evaluates.chain Evaluates.constant
  by_cases lower : 0 ≤ index - 1
  · apply Evaluates.Compares.next (rank_evaluates heap env index getIndex)
      (compared := .scalar (.bool true)) (afterComparison := heap)
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega
    · rfl
    · apply Evaluates.Compares.last (value := .scalar (.int items.length)) (middle := heap)
      · exact Evaluates.builtin (.cons (Evaluates.lookup getRows) .nil)
          (by simp [primitive, Mutable.length, found])
      · simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega
  · have rejected : decide (0 ≤ index - 1 ∧ index - 1 < items.length) = false := by simp only [lower, false_and, decide_false]
    rw [rejected]
    exact Evaluates.Compares.stop (rank_evaluates heap env index getIndex)
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega) rfl

private theorem ordered_member (rows : Rows heap collector addresses values)
    (member : value ∈ ordered heap addresses) :
    ∃ address digits, value = .ref address ∧ heap[address]? = some (.list (ints digits)) := by
  have original : value ∈ addresses.map Mutable.Value.ref :=
    (HeapSort.sortBy_perm _ (addresses.map Mutable.Value.ref)).mem_iff.mp member
  obtain ⟨address, addressMember, equal⟩ := List.mem_map.mp original
  obtain ⟨digits, _, found⟩ := rows.find addressMember
  exact ⟨address, digits, equal.symm, found⟩

private theorem select_result (heap : Mutable.Heap) (env : HeapCalls.Env) (index : Int)
    (address : Nat) (items : List Mutable.Value)
    (getIndex : env "idx" = some (.scalar (.int index))) (getRows : env "ps" = some (.ref address))
    (found : heap[address]? = some (.list items))
    (typed : ∀ value ∈ items, ∃ address digits, value = .ref address ∧ heap[address]? = some (.list (ints digits))) :
    ∃ resultAddress finalHeap digits,
      Evaluates program env answerExpression heap (.ref resultAddress) finalHeap ∧
      finalHeap[resultAddress]? = some (.list (ints digits)) ∧
      digits = selectRow (items.map (HeapSort.readInts heap)) index ∧
      ∀ collector, Preserves heap finalHeap collector := by
  have condition := bounds_evaluates heap env index address items getIndex getRows found
  by_cases valid : 0 ≤ index - 1 ∧ index - 1 < items.length
  · have bound : (index - 1).toNat < items.length := by omega
    obtain ⟨resultAddress, digits, item, contents⟩ := typed items[(index - 1).toNat] (List.getElem_mem bound)
    refine ⟨resultAddress, heap, digits, ?_, contents, ?_, fun _ _ _ _ h => h⟩
    · apply Evaluates.conditional condition (flag := true)
        (by simp only [show decide (0 ≤ index - 1 ∧ index - 1 < items.length) = true from decide_eq_true valid]; rfl)
      apply Evaluates.subscript (by intros; simp [rankExpression]) (Evaluates.lookup getRows) (rank_evaluates heap env index getIndex)
      have selected := Mutable.getItem_list heap address (index - 1).toNat items found bound
      simpa only [Int.toNat_of_nonneg valid.1, item] using selected
    · simp only [selectRow, List.length_map, if_pos valid, List.getElem?_map,
        List.getElem?_eq_getElem bound, Option.map_some, Option.getD_some, item, read_ints contents]
  · refine ⟨heap.length, heap ++ [.list []], [], ?_, by simp [ints], ?_, appended heap [.list []]⟩
    · exact Evaluates.conditional condition (flag := false)
        (by simp only [show decide (0 ≤ index - 1 ∧ index - 1 < items.length) = false from decide_eq_false valid]; rfl)
        (Evaluates.list .nil)
    · simp only [selectRow, List.length_map, if_neg valid]


private abbrev naiveArgs : List Arg :=
  [⟨"digits", some (.subscript (.name "list") (.name "int")), none⟩,
   ⟨"idx", some (.name "int"), none⟩]

/-- The reference terminates with an integer list and preserves every input object. -/
theorem naive.result (heap : Mutable.Heap) (address : Nat) (digits : List Int) (index : Int)
    (found : heap[address]? = some (.list (ints digits))) :
    ∃ resultAddress finalHeap output,
      ReturnsValue program "naive" [.ref address, .scalar (.int index)] heap (.ref resultAddress) finalHeap ∧
      finalHeap[resultAddress]? = some (.list (ints output)) ∧
      output = reference digits index ∧
      (∀ (location : Nat) (object : Mutable.Object), heap[location]? = some object → finalHeap[location]? = some object) := by
  let env := argumentEnv naiveArgs [.ref address, .scalar (.int index)]
  obtain ⟨middle, addresses, sorted, rows, saved⟩ := sorted_expression heap address digits env rfl found
  let items := ordered middle addresses
  let afterSort := middle ++ [Mutable.Object.list items]
  let afterAssign := setLocal env "ps" (.ref middle.length)
  have rowContents : ∀ value ∈ items, ∃ address digits,
      value = Mutable.Value.ref address ∧ afterSort[address]? = some (.list (ints digits)) := by
    intro value member
    obtain ⟨rowAddress, row, equal, contents⟩ := ordered_member rows member
    exact ⟨rowAddress, row, equal, found_append contents _⟩
  obtain ⟨resultAddress, finalHeap, output, selected, contents, equal, preserved⟩ :=
    select_result afterSort afterAssign index middle.length items rfl rfl (by simp [afterSort]) rowContents
  refine ⟨resultAddress, finalHeap, output, ?_, contents, ?_, ?_⟩
  · apply BlockReturns.function rfl rfl
    exact BlockReturns.assign sorted (BlockReturns.return_value selected)
  · have projection : items.map (HeapSort.readInts afterSort) = items.map (HeapSort.readInts middle) := by
      apply List.map_congr_left
      intro value member
      obtain ⟨rowAddress, row, rfl, contents⟩ := ordered_member rows member
      rw [read_ints contents, read_ints (found_append contents [Mutable.Object.list items])]
    rw [projection, ordered_project rows] at equal
    exact equal
  · have stable := (saved.trans (appended middle [.list items] heap.length)).trans (preserved heap.length)
    intro location object original
    exact stable location object (by have := inside original; omega) original

theorem naive.«Returns» (heap : Mutable.Heap) (address : Nat) (index : Int) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "naive" [.ref address, .scalar (.int index)] heap).Returns := by
  obtain ⟨digits, found⟩ := Mutable.Value.ints_of_hasType typed
  obtain ⟨_, _, _, returned, _, _⟩ := naive.result heap address digits index found
  exact returned.returns

theorem naive.«Supported» (heap : Mutable.Heap) (address : Nat) (index : Int) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "naive" [.ref address, .scalar (.int index)] heap).Supported :=
  (naive.«Returns» heap address index valid typed).supported


private def textValues (digits : List Int) : List Mutable.Value :=
  digits.map fun digit => .scalar (.string (toString digit))

private abbrev textElement := Expr.builtinCall .str [.name "digit"]

private theorem text_loop (heap : Mutable.Heap) (address : Nat) (digits remaining : List Int)
    (found : heap[address]? = some (.list (ints digits))) (position : Nat)
    (suffix : digits.drop position = remaining) (collected : List Int) (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env
      [.sequenceStepLoop "digit" (.ref address) position [.comprehensionAppend heap.length textElement] []]
      (heap ++ [.list (textValues collected)]) finalEnv
      (heap ++ [.list (textValues (collected ++ remaining))]) := by
  have sequence (collected : List Int) :
      Mutable.sequence (.ref address) (heap ++ [.list (textValues collected)]) =
        some (.ok (ints digits), heap ++ [.list (textValues collected)]) := by
    simp [Mutable.sequence, List.getElem?_append_left (inside found), found]
  induction remaining generalizing position collected env with
  | nil =>
      simp only [List.append_nil]
      refine ⟨env, BlockContinues.sequence_done (source := .ref address) (sequence collected) ?_ .nil⟩
      have exhausted : digits[position]? = none := by
        simpa [suffix] using (List.head?_drop (l := digits) (i := position)).symm
      simp [ints, List.getElem?_map, exhausted]
  | cons head tail ih =>
      let bound := setLocal env "digit" (.scalar (.int head))
      have converted : Evaluates program bound textElement
          (heap ++ [.list (textValues collected)]) (.scalar (.string (toString head)))
          (heap ++ [.list (textValues collected)]) := by
        exact Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil) rfl
      have emitted : BlockContinues program bound [.comprehensionAppend heap.length textElement]
          (heap ++ [.list (textValues collected)]) bound (heap ++ [.list (textValues (collected ++ [head]))]) := by
        have written := BlockContinues.comprehension_append (address := heap.length) converted
          (by simp : (heap ++ [.list (textValues collected)])[heap.length]? = some (.list (textValues collected)))
        simpa [textValues] using written
      obtain ⟨finalEnv, rest⟩ := ih (position + 1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) (collected ++ [head]) bound
      refine ⟨finalEnv, ?_⟩
      have item : digits[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := digits) (i := position)).symm
      apply BlockContinues.sequence_step (source := .ref address) (value := .scalar (.int head))
        (sequence collected) (by simp [ints, List.getElem?_map, item])
      simpa [Calls.loopContinuation, Calls.loopControl, List.append_assoc] using emitted.append rest

/-- String conversion consumes the actual reference result, including empty out-of-range results. -/
theorem naive_text.result (heap : Mutable.Heap) (address : Nat) (digits : List Int) (index : Int)
    (found : heap[address]? = some (.list (ints digits))) :
    ∃ (output : List Int) (finalHeap : Mutable.Heap),
      ReturnsValue program "naive_text" [.ref address, .scalar (.int index)] heap
        (.scalar (.string (String.intercalate "" (output.map toString)))) finalHeap ∧
      output = reference digits index ∧
      (∀ (location : Nat) (object : Mutable.Object), heap[location]? = some object → finalHeap[location]? = some object) := by
  obtain ⟨rowAddress, middle, output, returned, contents, equal, preserved⟩ := naive.result heap address digits index found
  let env := argumentEnv naiveArgs [.ref address, .scalar (.int index)]
  let iterable := Expr.call (.name "naive") [.name "digits", .name "idx"]
  let generators : List (Expr × Expr × List Expr) := [(.name "digit", iterable, [])]
  obtain ⟨finalEnv, collected⟩ := text_loop middle rowAddress output output contents 0 rfl []
    (comprehensionTargetsEnv env generators)
  refine ⟨output, middle ++ [.list (textValues output)], ?_, equal, ?_⟩
  swap
  · intro location object original
    exact found_append (preserved location object original) _
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.consume_generator_join Evaluates.constant
  apply GeneratorCollects.sequence (finalEnv := finalEnv) (items := ints output) (source := .ref rowAddress)
    (middle := middle) (collectedHeap := middle ++ [.list (textValues output)])
    (by intro expressions; simp)
    (by intro expressions; simp)
    (by intro expressions; simp)
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) returned
  · simp [Mutable.sequence, contents]
  · exact collected
  · exact primitive_join_list _ middle.length "" (output.map toString) (by simp [textValues, List.map_map])

private theorem extension_of_preserved (before after : Mutable.Heap)
    (preserved : ∀ (location : Nat) (object : Mutable.Object),
      before[location]? = some object → after[location]? = some object) :
    ∃ extra, after = before ++ extra := by
  induction before generalizing after with
  | nil => exact ⟨after, rfl⟩
  | cons first rest ih =>
      have head := preserved 0 first rfl
      cases after with
      | nil => cases head
      | cons next tail =>
          have same : next = first := Option.some.inj head
          subst next
          obtain ⟨extra, equal⟩ := ih tail (fun position object found => preserved (position + 1) object found)
          exact ⟨extra, by simp [equal]⟩

/-- Exact output of the original Python reference, preserving the original heap prefix. -/
theorem naive_text.exact_result (heap : Mutable.Heap) (address : Nat) (digits : List Int) (index : Int)
    (found : heap[address]? = some (.list (digits.map fun n => .scalar (.int n)))) :
    ∃ extra, ReturnsValue program "naive_text" [.ref address, .scalar (.int index)] heap
      (.scalar (.string (String.intercalate "" ((reference digits index).map toString)))) (heap ++ extra) := by
  obtain ⟨output, finalHeap, returned, equal, preserved⟩ := naive_text.result heap address digits index found
  obtain ⟨extra, rfl⟩ := extension_of_preserved heap finalHeap preserved
  exact ⟨extra, equal ▸ returned⟩

theorem naive_text.«Returns» (heap : Mutable.Heap) (address : Nat) (index : Int) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "naive_text" [.ref address, .scalar (.int index)] heap).Returns := by
  obtain ⟨digits, found⟩ := Mutable.Value.ints_of_hasType typed
  obtain ⟨_, _, returned, _⟩ := naive_text.result heap address digits index found
  exact returned.returns

theorem naive_text.«Supported» (heap : Mutable.Heap) (address : Nat) (index : Int) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.call program "naive_text" [.ref address, .scalar (.int index)] heap).Supported :=
  (naive_text.«Returns» heap address index valid typed).supported

end data.«project-euler-statements».data.py.project_euler_statements.p24
