import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p35.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.SumCalls
import lang.py.FormalSW.TruthCalls
import ProjectEulerStatements.Lib.CircularPrimes
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Range

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p35
open FormalSW.PyAst HeapCalls
private abbrev program := P35Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (items : List Nat) : List Mutable.Value := items.map number

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 4 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["rotations", "is_circular_prime", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem found_append {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) (extra : Mutable.Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private abbrev rotation : Expr := .binOp
  (.subscript (.name "xs") (.slice (some (.name "i")) none none)) .add
  (.subscript (.name "xs") (.slice none (some (.name "i")) none))

/-- Each rotation evaluates its suffix first, then prefix, then concatenation. -/
private theorem rotation.result (items : List Nat) (index : Nat) (within : index ≤ items.length)
    (heap : Mutable.Heap) (address : Nat) (found : heap[address]? = some (.list (numbers items)))
    (env : HeapCalls.Env) (getXs : env "xs" = some (.ref address)) (getI : env "i" = some (number index)) :
    Evaluates program env rotation heap (.ref (heap.length + 2))
      (heap ++ [.list (numbers (items.drop index)), .list (numbers (items.take index)),
        .list (numbers (items.drop index ++ items.take index))]) := by
  let first := heap ++ [Mutable.Object.list (numbers (items.drop index))]
  let second := first ++ [Mutable.Object.list (numbers (items.take index))]
  have suffix : Evaluates program env
      (.subscript (.name "xs") (.slice (some (.name "i")) none none))
      heap (.ref heap.length) first := by
    apply Evaluates.slice (.cons (Evaluates.lookup getXs) (.cons (Evaluates.lookup getI)
      (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
    simpa [first, numbers] using Mutable.getSlice_list_suffix heap address (numbers items) index found
  have slicePrefix : Evaluates program env (.subscript (.name "xs") (.slice none (some (.name "i")) none))
      first (.ref first.length) second := by
    apply Evaluates.slice (.cons (Evaluates.lookup getXs)
      (.cons Evaluates.constant (.cons (Evaluates.lookup getI) (.cons Evaluates.constant .nil))))
    simpa [second, numbers, FormalSW.Py.Builtin.Slice.prefixLength_nonnegative, Nat.min_eq_left within] using
      Mutable.getSlice_list_prefix first address (numbers items) index (found_append found _)
  apply Evaluates.binary suffix slicePrefix
  dsimp only [Mutable.binary]
  simp only [show (BinOp.add == BinOp.add) = true from rfl, if_true]
  simp [Mutable.array, Mutable.allocate, Except.map, first, second, numbers,
    List.map_append, List.append_assoc]

private theorem digits_be_result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "digits_be" [number n] heap (.ref (heap.length + 1))
      (heap ++ [.list (numbers (Nat.digits 10 n)), .list (numbers (ProjectEulerStatements.P35.digitsBE n))]) := by
  have executed := common.digits_be.result n 10 (by omega) heap
  have defaulted := ReturnsValue.with_defaults (supplied := [number n]) rfl rfl rfl executed
  simpa only [numbers, number, ProjectEulerStatements.P35.digitsBE, List.map_reverse] using
    defaulted.extend common_extension

private theorem of_digits_be_result (items : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue program "of_digits_be" [.ref address] heap
      (number (ProjectEulerStatements.P35.digitsToNat items))
      (heap ++ [.list (numbers items.reverse)]) := by
  have executed := common.of_digits_be.result (items.map (fun (n : Nat) => (n : Int))) 10 heap address
    (by simpa [numbers, number, List.map_map] using found)
  have naturalValue : ProjectEulerStatements.PositionalDigits.value 10
      ((items.map (fun (n : Nat) => (n : Int))).reverse) = ((Nat.ofDigits 10 items.reverse : Nat) : Int) := by
    simpa only [Nat.cast_ofNat, List.map_reverse] using
      ProjectEulerStatements.PositionalDigits.value_naturals 10 items.reverse
  rw [naturalValue] at executed
  have defaulted := ReturnsValue.with_defaults (supplied := [.ref address]) rfl rfl rfl executed
  simpa only [numbers, number, ProjectEulerStatements.P35.digitsToNat, List.map_reverse, List.map_map] using
    defaulted.extend common_extension

private def Preserves (before after : Mutable.Heap) (collector : Nat) : Prop :=
  ∀ address object, address ≠ collector → before[address]? = some object → after[address]? = some object

private theorem Preserves.trans (first : Preserves before middle collector)
    (second : Preserves middle after collector) : Preserves before after collector :=
  fun address object other found => second address object other (first address object other found)

private theorem appended (heap extra : Mutable.Heap) (collector : Nat) : Preserves heap (heap ++ extra) collector :=
  fun _ _ _ found => found_append found extra

private theorem updated (heap : Mutable.Heap) (collector : Nat) (object : Mutable.Object) :
    Preserves heap (heap.set collector object) collector := by
  intro address value other found
  simpa [List.getElem?_set_ne other.symm] using found

/-- Rotation rows retain the fresh list identities created by slicing and addition. -/
def Rows (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat) (rows : List (List Nat)) : Prop :=
  List.Forall₂ (fun address row => collector < address ∧ heap[address]? = some (.list (numbers row))) addresses rows

private theorem Rows.preserve {heap finalHeap : Mutable.Heap} {collector : Nat}
    {addresses : List Nat} {rows : List (List Nat)} (related : Rows heap collector addresses rows)
    (preserved : Preserves heap finalHeap collector) : Rows finalHeap collector addresses rows := by
  induction related with
  | nil => exact .nil
  | @cons address row addresses rows first rest ih =>
      exact .cons ⟨first.1, preserved address _ (by omega) first.2⟩ ih

private abbrev collectBody (collector : Nat) : List Stmt := [.comprehensionAppend collector rotation]
private def rotationSlice (items : List Nat) (first count : Nat) : List (List Nat) :=
  (List.range' first count).map (fun i => items.drop i ++ items.take i)

private theorem collect_rotations (items : List Nat) (first count : Nat) (bound : first + count = items.length)
    (before : List (List Nat)) (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat)
    (found : heap[collector]? = some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses before) (input : Nat) (separate : input ≠ collector)
    (inputFound : heap[input]? = some (.list (numbers items))) (env : HeapCalls.Env)
    (getXs : env "xs" = some (.ref input)) :
    ∃ finalHeap finalEnv finalAddresses,
      BlockContinues program env [.rangeStepLoop "i" first items.length 1 (collectBody collector) []]
        heap finalEnv finalHeap ∧
      finalHeap[collector]? = some (.list (finalAddresses.map Mutable.Value.ref)) ∧
      Rows finalHeap collector finalAddresses (before ++ rotationSlice items first count) := by
  induction count generalizing first before heap addresses env with
  | zero =>
      refine ⟨heap, env, addresses, ?_, found, ?_⟩
      · exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) BlockContinues.nil
      · simpa [rotationSlice] using rows
  | succ count ih =>
      let boundEnv := setLocal env "i" (number first)
      let extra : Mutable.Heap := [.list (numbers (items.drop first)), .list (numbers (items.take first)),
        .list (numbers (items.drop first ++ items.take first))]
      let nextAddresses := addresses ++ [heap.length + 2]
      let nextHeap := (heap ++ extra).set collector (.list (nextAddresses.map Mutable.Value.ref))
      have inside : collector < heap.length := (List.getElem?_eq_some_iff.mp found).1
      have evaluated : Evaluates program boundEnv rotation heap (.ref (heap.length + 2)) (heap ++ extra) :=
        rotation.result items first (by omega) heap input inputFound boundEnv
          (by simpa [boundEnv, setLocal] using getXs) (by simp [boundEnv, setLocal])
      have emitted : BlockContinues program boundEnv (collectBody collector) heap boundEnv nextHeap := by
        simpa [nextHeap, nextAddresses] using
          BlockContinues.comprehension_append evaluated (found_append found extra)
      have nextFound : nextHeap[collector]? = some (.list (nextAddresses.map Mutable.Value.ref)) := by
        apply List.getElem?_set_self
        simp only [List.length_append]
        omega
      have preserved : Preserves heap nextHeap collector :=
        (appended heap extra collector).trans (updated _ collector _)
      have fresh : collector < heap.length + 2 ∧
          nextHeap[heap.length + 2]? = some (.list (numbers (items.drop first ++ items.take first))) := by
        refine ⟨by omega, ?_⟩
        change ((heap ++ extra).set collector _)[heap.length + 2]? = _
        rw [List.getElem?_set_ne (by omega : collector ≠ heap.length + 2)]
        simp [extra]
      have nextRows : Rows nextHeap collector nextAddresses (before ++ [items.drop first ++ items.take first]) :=
        List.rel_append (rows.preserve preserved) (.cons fresh .nil)
      obtain ⟨finalHeap, finalEnv, finalAddresses, rest, finalFound, finalRows⟩ :=
        ih (first + 1) (by omega) (before ++ [items.drop first ++ items.take first]) nextHeap nextAddresses
          nextFound nextRows (preserved input _ separate inputFound) boundEnv
          (by simpa [boundEnv, setLocal] using getXs)
      refine ⟨finalHeap, finalEnv, finalAddresses, ?_, finalFound, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, show Calls.loopControl (collectBody collector) = false from rfl,
          ↓reduceIte, Int.natCast_add, Int.natCast_one] using emitted.append rest
      · simpa [rotationSlice, List.range'_succ, List.append_assoc] using finalRows

/-- The complete comprehension materializes every rotation before its caller's `all`. -/
theorem rotations.result (items : List Nat) (heap : Mutable.Heap) (input : Nat)
    (inputFound : heap[input]? = some (.list (numbers items))) :
    ∃ finalHeap addresses, ReturnsValue program "rotations" [.ref input] heap (.ref heap.length) finalHeap ∧
      finalHeap[heap.length]? = some (.list (addresses.map Mutable.Value.ref)) ∧
      Rows finalHeap heap.length addresses (ProjectEulerStatements.P35.rotations items) := by
  let args := ((findFunctionIn program.body "rotations").getD ([], [])).1
  let code := ((findFunctionIn program.body "rotations").getD ([], [])).2
  let initial := functionEnv args code [.ref input] []
  let generators : List (String × Expr × List Expr) :=
    [("i", .call (.name "range") [.builtinCall .len [.name "xs"]], [])]
  have inside : input < heap.length := (List.getElem?_eq_some_iff.mp inputFound).1
  obtain ⟨finalHeap, finalEnv, addresses, collected, found, rows⟩ :=
    collect_rotations items 0 items.length (by omega) [] (heap ++ [.list []]) heap.length []
      (by simp) .nil input (by omega) (found_append inputFound _) (comprehensionEnv initial generators) rfl
  refine ⟨finalHeap, addresses, ?_, found, ?_⟩
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.list_comp_range (values := [number items.length]) (middle := heap) (finalEnv := finalEnv)
      (.cons (Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil) ?_) .nil) rfl collected
    simp [primitive, Mutable.length, inputFound, numbers]
  · simpa only [ProjectEulerStatements.P35.rotations, rotationSlice,
      List.nil_append, List.range_eq_range'] using rows

private theorem Rows.at {heap : Mutable.Heap} {collector : Nat} {addresses : List Nat}
    {rows : List (List Nat)} {row : List Nat} (related : Rows heap collector addresses rows)
    (position : Nat) (item : rows[position]? = some row) :
    ∃ address, addresses[position]? = some address ∧ heap[address]? = some (.list (numbers row)) := by
  induction related generalizing position with
  | nil => simp at item
  | @cons address head addresses rows first rest ih =>
      cases position with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at item
          subst row
          exact ⟨address, rfl, first.2⟩
      | succ position => exact ih position (by simpa using item)

private abbrev rotationPrime : Expr := .call (.name "is_prime")
  [.call (.name "of_digits_be") [.name "r"]]
private abbrev rowPrime (items : List Nat) : Bool :=
  ProjectEulerStatements.P35.isPrime (ProjectEulerStatements.P35.digitsToNat items)

private theorem rotationPrime.result (items : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) (env : HeapCalls.Env)
    (getR : env "r" = some (.ref address)) :
    Evaluates program env rotationPrime heap (.scalar (.bool (rowPrime items)))
      (heap ++ [.list (numbers items.reverse)]) := by
  apply Evaluates.call
    (.cons (Evaluates.call (.cons (Evaluates.lookup getR) .nil)
      (of_digits_be_result items heap address found)) .nil)
  exact (common.is_prime.heap_result (ProjectEulerStatements.P35.digitsToNat items) _).extend common_extension

/-- The lazy consumer stops before reversing any later row once a composite occurs. -/
private theorem all_rotations (rows remaining : List (List Nat)) (addresses : List Nat)
    (position collector : Nat) (heap : Mutable.Heap)
    (found : heap[collector]? = some (.list (addresses.map Mutable.Value.ref)))
    (related : Rows heap collector addresses rows) (suffix : rows.drop position = remaining) (env : HeapCalls.Env) :
    ∃ extra, BlockReturns program env
      [.sequenceStepLoop "r" (.ref collector) position (truthBody true rotationPrime) [],
        .return (.constant (.bool true))] heap (.scalar (.bool (remaining.all rowPrime))) (heap ++ extra) := by
  induction remaining generalizing position heap env with
  | nil =>
      refine ⟨[], ?_⟩
      simp only [List.append_nil]
      apply BlockReturns.sequence_done (source := .ref collector) (items := addresses.map Mutable.Value.ref)
        (by simp [sequenceValue, Mutable.sequence, found])
      · have missing : rows[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := rows) (i := position)).symm
        have length := List.Forall₂.length_eq related
        have outside := List.getElem?_eq_none_iff.mp missing
        simp [List.getElem?_eq_none (by omega : addresses.length ≤ position)]
      · exact BlockReturns.return_value Evaluates.constant
  | cons head tail ih =>
      have item : rows[position]? = some head := by
        simpa [suffix] using (List.head?_drop (l := rows) (i := position)).symm
      obtain ⟨address, selected, rowFound⟩ := related.at position item
      let boundEnv := setLocal env "r" (.ref address)
      let extra : Mutable.Heap := [.list (numbers head.reverse)]
      have tested := rotationPrime.result head heap address rowFound boundEnv (by simp [boundEnv, setLocal])
      cases flag : rowPrime head with
      | false =>
          refine ⟨extra, ?_⟩
          simp only [List.all_cons, flag, Bool.false_and]
          apply BlockReturns.sequence_step (source := .ref collector) (value := .ref address)
            (items := addresses.map Mutable.Value.ref)
            (by simp [sequenceValue, Mutable.sequence, found]) (by simp [selected])
          apply BlockReturns.branch (flag := false) (by simpa only [flag] using tested) rfl
          exact BlockReturns.return_value Evaluates.constant
      | true =>
          obtain ⟨tailExtra, rest⟩ := ih (position + 1) (heap ++ extra)
            (found_append found extra) (related.preserve (appended heap extra collector))
            (by simp [List.drop_add_one_eq_tail_drop, suffix]) boundEnv
          refine ⟨extra ++ tailExtra, ?_⟩
          simp only [List.all_cons, flag, Bool.true_and]
          apply BlockReturns.sequence_step (source := .ref collector) (value := .ref address)
            (items := addresses.map Mutable.Value.ref)
            (by simp [sequenceValue, Mutable.sequence, found]) (by simp [selected])
          apply BlockReturns.branch (flag := true) (by simpa only [flag] using tested) rfl
          simpa [truthBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            extra, numbers, List.append_assoc] using rest

private abbrev rotationsExpr : Expr := .call (.name "rotations")
  [.call (.name "digits_be") [.name "n"]]
private abbrev circularAll : Expr := .consumeGenerator (.builtinCall .all []) rotationPrime
  [(.name "r", rotationsExpr, [])]

theorem is_circular_prime.result (n : Nat) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "is_circular_prime" [number n] heap
      (.scalar (.bool (ProjectEulerStatements.P35.isCircularPrime n))) finalHeap := by
  let args := ((findFunctionIn program.body "is_circular_prime").getD ([], [])).1
  let code := ((findFunctionIn program.body "is_circular_prime").getD ([], [])).2
  let env := functionEnv args code [number n] []
  have guard : Evaluates program env (.compare (.name "n") [(.gtE, .constant (.int 2))]) heap
      (.scalar (.bool (decide (2 ≤ n)))) heap := by
    apply Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  by_cases small : n < 2
  · refine ⟨heap, ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    simp only [ProjectEulerStatements.P35.isCircularPrime, small, ↓reduceIte]
    apply Evaluates.boolean_stop (flag := false) (by simpa [show ¬ 2 ≤ n by omega] using guard) rfl rfl
  · let digits := ProjectEulerStatements.P35.digitsBE n
    let initialHeap := heap ++ [.list (numbers (Nat.digits 10 n)), .list (numbers digits)]
    obtain ⟨rotationHeap, addresses, rotated, found, rows⟩ :=
      rotations.result digits initialHeap (heap.length + 1) (by simp [initialHeap])
    have iterator : Evaluates program env rotationsExpr heap (.ref initialHeap.length) rotationHeap :=
      Evaluates.call (.cons (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (digits_be_result n heap)) .nil) rotated
    let generators : List (Expr × Expr × List Expr) := [(.name "r", rotationsExpr, [])]
    obtain ⟨extra, checked⟩ := all_rotations (ProjectEulerStatements.P35.rotations digits)
      (ProjectEulerStatements.P35.rotations digits) addresses 0 initialHeap.length rotationHeap
      found rows rfl (comprehensionTargetsEnv env generators)
    refine ⟨rotationHeap ++ extra, ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    simp only [ProjectEulerStatements.P35.isCircularPrime, small, ↓reduceIte,
      ProjectEulerStatements.CircularPrimes.listAll_map_eq_all]
    apply Evaluates.boolean_next (flag := true) (by simpa [show 2 ≤ n by omega] using guard) rfl rfl
    apply Evaluates.boolean_last
      (value := .scalar (.bool ((ProjectEulerStatements.P35.rotations digits).all rowPrime)))
    · apply Evaluates.truth_generator_sequence (universal := true) (items := addresses.map Mutable.Value.ref)
        (by intro expressions; simp [rotationsExpr])
        (by intro expressions; simp [rotationsExpr])
        (by intro expressions; simp [rotationsExpr]) iterator
        (by simp [Mutable.sequence, found])
      exact checked
    · rfl

private abbrev countTest : Expr := .call (.name "is_circular_prime") [.name "n"]
private abbrev countBody : List Stmt := comprehensionFilters [countTest] (sumBody (.constant (.int 1)) [])
private def countFrom (first count total : Nat) : Nat :=
  (List.range' first count).foldl
    (fun acc n => if ProjectEulerStatements.P35.isCircularPrime n then acc + 1 else acc) total

private theorem naive.loop (count first total : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getTotal : env sumAccumulator = some (number total)) :
    ∃ finalHeap, BlockReturns program env
      [.rangeStepLoop "n" first (first + count) 1 countBody [], .return (.name sumAccumulator)]
      heap (number (countFrom first count total)) finalHeap := by
  induction count generalizing first total heap env with
  | zero =>
      refine ⟨heap, ?_⟩
      apply BlockReturns.range_done (by simp [Calls.rangeContinues])
      exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let boundEnv := setLocal env "n" (number first)
      obtain ⟨middle, predicate⟩ := is_circular_prime.result first heap
      have tested : Evaluates program boundEnv countTest heap
          (.scalar (.bool (ProjectEulerStatements.P35.isCircularPrime first))) middle :=
        Evaluates.call (.cons (Evaluates.lookup (by simp [boundEnv, setLocal])) .nil) predicate
      cases yes : ProjectEulerStatements.P35.isCircularPrime first with
      | true =>
          let nextEnv := setLocal boundEnv sumAccumulator (number (total + 1))
          obtain ⟨finalHeap, continued⟩ := ih (first + 1) (total + 1) middle nextEnv
            (by simp [nextEnv, setLocal])
          refine ⟨finalHeap, ?_⟩
          apply BlockReturns.range_step (by simp [Calls.rangeContinues])
          apply BlockReturns.branch (flag := true) (by simpa [yes] using tested) rfl
          apply BlockReturns.assign (value := number (total + 1)) (middle := middle)
          · apply Evaluates.binary (av := number total) (bv := number 1)
              (Evaluates.lookup (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal)) Evaluates.constant
            simp [Mutable.binary, scalarBinary, number]
          · simpa [countBody, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
              Calls.loopControlStmt, countFrom, List.range'_succ, List.foldl_cons, yes, nextEnv, boundEnv,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm] using continued
      | false =>
          obtain ⟨finalHeap, continued⟩ := ih (first + 1) total middle boundEnv
            (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal)
          refine ⟨finalHeap, ?_⟩
          apply BlockReturns.range_step (by simp [Calls.rangeContinues])
          apply BlockReturns.branch (flag := false) (by simpa [yes] using tested) rfl
          simpa [countBody, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt, countFrom, List.range'_succ, List.foldl_cons, yes, boundEnv,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Int.add_assoc, Int.add_comm, Int.add_left_comm] using continued

private theorem countFrom_naive (limit : Nat) :
    countFrom 0 limit 0 = ProjectEulerStatements.P35.naive limit := by
  rw [ProjectEulerStatements.CircularPrimes.naive_fold]
  simp only [countFrom, List.range_eq_range']

theorem naive.result (limit : Nat) (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive" [number limit] heap
      (number (ProjectEulerStatements.P35.naive limit)) finalHeap := by
  let env := functionEnv [⟨"limit", some (.name "int"), none⟩]
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number limit] []
  let summed := setLocal (comprehensionEnv env
    [("n", .call (.name "range") [.name "limit"], [countTest])]) sumAccumulator (number 0)
  obtain ⟨finalHeap, loop⟩ := naive.loop limit 0 0 heap summed rfl
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range (values := [number limit]) (middle := heap)
    (.cons (Evaluates.lookup rfl) .nil) rfl Evaluates.constant rfl
  simpa only [Nat.zero_add, Nat.cast_zero, Int.zero_add, countFrom_naive] using loop

theorem naive.«Returns» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P35Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Returns := by
  have nonnegative : 0 ≤ limit := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  lift limit to Nat using nonnegative
  obtain ⟨_, returned⟩ := naive.result limit []
  exact returned.scalar_returns

theorem naive.«Supported» (limit : Int)
    (condition : Calls.Condition program (fun name => if name = "limit" then some (.int limit) else none)
      P35Ast.requires_naive_0) : (HeapCalls.scalarFunction program "naive" [.int limit]).Supported :=
  (naive.«Returns» limit condition).supported

end data.«project-euler-statements».data.py.project_euler_statements.p35
