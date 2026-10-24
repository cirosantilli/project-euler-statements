import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p33.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerStatements.Lib.DigitCancellingCertificate
import Mathlib.Data.List.Forall2

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p33
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.P33
private abbrev program := P33Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (items : List Nat) : List Mutable.Value := items.map number

private theorem found_append {heap : Mutable.Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) (extra : Mutable.Heap) :
    (heap ++ extra)[address]? = some object := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- Early-return counterparts of the ordinary enumerate loop rules. -/
private theorem returns_for_enumerate
    (iterable : Evaluates program env expression heap source middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (rest : BlockReturns program env
      (.enumerateStepLoop index name (sequenceSource source) 0 0 body otherwise :: following)
      middle answer finalHeap) :
    BlockReturns program env
      (.forIn (.tuple [.name index, .name name]) (.call (.name "enumerate") [expression])
        body otherwise :: following) heap answer finalHeap := by
  intro anchors stack
  exact .next rfl ((iterable anchors _).trans (.next rfl (.next rfl
    (.next (by simp [step, run, enumerateStart, sequence]) (rest anchors stack)))))

private theorem returns_enumerate_step
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : BlockReturns program (setLocal (setLocal env index (.scalar (.int counter))) name value)
      (body ++ Calls.loopContinuation body
        (.enumerateStepLoop index name source (position + 1) (counter + 1) body otherwise) :: following)
      heap answer finalHeap) :
    BlockReturns program env
      (.enumerateStepLoop index name source position counter body otherwise :: following)
      heap answer finalHeap := by
  intro anchors stack
  refine .next ?_ (rest anchors stack)
  simp [step, run, sequence, item, List.append_assoc]

private theorem returns_enumerate_done
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (finished : items[position]? = none)
    (rest : BlockReturns program env (otherwise ++ following) heap answer finalHeap) :
    BlockReturns program env
      (.enumerateStepLoop index name source position counter body otherwise :: following)
      heap answer finalHeap :=
  fun anchors stack => .next (by simp [step, run, sequence, finished]) (rest anchors stack)

/-- Slicing and concatenation preserve input objects and allocate three fresh lists. -/
theorem erase_nth.result (items : List Nat) (index : Nat) (within : index ≤ items.length)
    (heap : Mutable.Heap) (address : Nat) (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue program "erase_nth" [.ref address, number index] heap (.ref (heap.length + 2))
      (heap ++ [.list (numbers (items.take index)), .list (numbers (items.drop (index + 1))),
        .list (numbers (eraseNth items index))]) := by
  let args := ((findFunctionIn program.body "erase_nth").getD ([], [])).1
  let body := ((findFunctionIn program.body "erase_nth").getD ([], [])).2
  let env := functionEnv args body [.ref address, number index] []
  let first := heap ++ [Mutable.Object.list (numbers (items.take index))]
  let second := first ++ [Mutable.Object.list (numbers (items.drop (index + 1)))]
  have slicePrefix : Evaluates program env (.subscript (.name "xs") (.slice none (some (.name "i")) none))
      heap (.ref heap.length) first := by
    apply Evaluates.slice (.cons (Evaluates.lookup rfl)
      (.cons Evaluates.constant (.cons (Evaluates.lookup rfl) (.cons Evaluates.constant .nil))))
    simpa [first, numbers, FormalSW.Py.Builtin.Slice.prefixLength_nonnegative, Nat.min_eq_left within] using
      Mutable.getSlice_list_prefix heap address (numbers items) index found
  have suffix : Evaluates program env
      (.subscript (.name "xs") (.slice (some (.binOp (.name "i") .add (.constant (.int 1)))) none none))
      first (.ref first.length) second := by
    apply Evaluates.slice (.cons (Evaluates.lookup rfl) (.cons
      (Evaluates.binary (value := number (index + 1)) (finalHeap := first)
        (Evaluates.lookup rfl) Evaluates.constant (by simp [Mutable.binary, scalarBinary, number]))
      (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
    simpa [second, numbers] using
      Mutable.getSlice_list_suffix first address (numbers items) (index + 1) (found_append found _)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary slicePrefix suffix
  dsimp only [Mutable.binary]
  simp only [show (BinOp.add == BinOp.add) = true from rfl, if_true]
  simp [Mutable.array, Mutable.allocate, Except.map, first, second, numbers,
    eraseNth, List.map_append, List.append_assoc]

set_option maxRecDepth 10000 in
private theorem bounded_digits : ∀ n : Fin 100,
    Nat.digits 10 n.val = if n.val = 0 then [] else if n.val < 10 then [n.val] else [n.val % 10, n.val / 10] := by
  decide +kernel

private theorem decimal_digits (n : Nat) (bounded : n < 100) :
    Nat.digits 10 n = if n = 0 then [] else if n < 10 then [n] else [n % 10, n / 10] :=
  bounded_digits ⟨n, bounded⟩

private theorem decimal_guard (n d : Nat) (smallN : n < 100) (smallD : d < 100) :
    ((Nat.digits 10 n).length = (Nat.digits 10 d).length ∧
      2 ≤ (Nat.digits 10 n).length ∧ n < d) ↔ 10 ≤ n ∧ 10 ≤ d ∧ n < d := by
  rw [decimal_digits n smallN, decimal_digits d smallD]
  split_ifs <;> simp_all

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 5 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["erase_nth", "is_curious", "curious_fractions", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

private theorem of_digits_result (items : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue program "of_digits_le" [.ref address] heap (number (Nat.ofDigits 10 items)) heap := by
  have executed := common.of_digits_le.result (items.map (fun (n : Nat) => (n : Int))) 10 heap address
    (by simpa [numbers, number, List.map_map] using found)
  have naturalValue : ProjectEulerStatements.PositionalDigits.value 10
      (items.map (fun (n : Nat) => (n : Int))) = ((Nat.ofDigits 10 items : Nat) : Int) := by
    simpa only [Nat.cast_ofNat] using
      ProjectEulerStatements.PositionalDigits.value_naturals 10 items
  rw [naturalValue] at executed
  exact (ReturnsValue.with_defaults (supplied := [.ref address]) rfl rfl rfl executed).extend common_extension

private abbrev curiousCode : List Stmt :=
  executableBody ((findFunctionIn program.body "is_curious").getD ([], [])).2
private abbrev outerCode : List Stmt := match (curiousCode[2]? : Option Stmt) with
  | some (.forIn _ _ body _) => body
  | _ => []
private abbrev innerCode : List Stmt := match (outerCode[0]? : Option Stmt) with
  | some (.forIn _ _ body _) => body
  | _ => []

/-- A true test returns through every enclosing loop; a false test resumes its caller. -/
private def Checked (env : HeapCalls.Env) (body : List Stmt) (heap : Mutable.Heap)
    (finalEnv : HeapCalls.Env) (finalHeap : Mutable.Heap) (accepted : Bool) : Prop :=
  if accepted then ∀ following, BlockReturns program env (body ++ following) heap (.scalar (.bool true)) finalHeap
  else BlockContinues program env body heap finalEnv finalHeap

private theorem Checked.prepend
    (first : BlockContinues program env body heap middleEnv middleHeap)
    (rest : Checked middleEnv following middleHeap finalEnv finalHeap accepted) :
    Checked env (body ++ following) heap finalEnv finalHeap accepted := by
  cases accepted with
  | false => exact first.append rest
  | true =>
      intro remaining
      simpa only [List.append_assoc] using first.returns (rest remaining)

private structure LoopLocals (env : HeapCalls.Env) (n d dn dd : Nat) : Prop where
  numerator : env "n" = some (number n)
  denominator : env "d" = some (number d)
  numeratorDigits : env "dn" = some (.ref dn)
  denominatorDigits : env "dd" = some (.ref dd)

private theorem LoopLocals.other (locals : LoopLocals env n d dn dd) (name : String) (value : Mutable.Value)
    (different : name ≠ "n" ∧ name ≠ "d" ∧ name ≠ "dn" ∧ name ≠ "dd") :
    LoopLocals (setLocal env name value) n d dn dd := by
  rcases locals with ⟨a, b, c, e⟩
  constructor
  · simpa only [setLocal, if_neg (Ne.symm different.1)] using a
  · simpa only [setLocal, if_neg (Ne.symm different.2.1)] using b
  · simpa only [setLocal, if_neg (Ne.symm different.2.2.1)] using c
  · simpa only [setLocal, if_neg (Ne.symm different.2.2.2)] using e

private structure RowLocals (env : HeapCalls.Env) (n d dn dd i x : Nat) : Prop extends LoopLocals env n d dn dd where
  index : env "i" = some (number i)
  digit : env "x" = some (number x)

private theorem RowLocals.other (locals : RowLocals env n d dn dd i x) (name : String) (value : Mutable.Value)
    (different : name ≠ "n" ∧ name ≠ "d" ∧ name ≠ "dn" ∧ name ≠ "dd" ∧ name ≠ "i" ∧ name ≠ "x") :
    RowLocals (setLocal env name value) n d dn dd i x := by
  constructor
  · exact locals.toLoopLocals.other name value ⟨different.1, different.2.1, different.2.2.1, different.2.2.2.1⟩
  · simpa [setLocal, Ne.symm different.2.2.2.2.1] using locals.index
  · simpa [setLocal, Ne.symm different.2.2.2.2.2] using locals.digit

private def attempt (n d : Nat) (dn dd : List Nat) (i x j y : Nat) : Bool :=
  if x = y ∧ x ≠ 0 then
    decide (n * Nat.ofDigits 10 (eraseNth dd j) = d * Nat.ofDigits 10 (eraseNth dn i))
  else false

private abbrev erasedObjects (items : List Nat) (index : Nat) : Mutable.Heap :=
  [.list (numbers (items.take index)), .list (numbers (items.drop (index + 1))),
    .list (numbers (eraseNth items index))]

private theorem common_digit (x y : Nat) (env : HeapCalls.Env) (heap : Mutable.Heap)
    (getX : env "x" = some (number x)) (getY : env "y" = some (number y)) :
    Evaluates program env (.boolOp .and
      [.compare (.name "x") [(.eq, .name "y")], .compare (.name "x") [(.notEq, .constant (.int 0))]])
      heap (.scalar (.bool (decide (x = y ∧ x ≠ 0)))) heap := by
  by_cases same : x = y
  · have reduced : (x = y ∧ x ≠ 0) = (x ≠ 0) := propext ⟨And.right, fun h => ⟨same, h⟩⟩
    simp only [reduced]
    apply Evaluates.boolean_next (value := .scalar (.bool true)) (middle := heap) (flag := true)
    · exact Evaluates.compare (Evaluates.lookup getX) (Evaluates.lookup getY)
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, same])
    · rfl
    · rfl
    · apply Evaluates.boolean_last (value := .scalar (.bool (decide (x ≠ 0))))
      · apply Evaluates.compare (Evaluates.lookup getX) Evaluates.constant
        simp [HeapCalls.compare, scalarCompare, evalCmpOp]
      · rfl
  · have reduced : (x = y ∧ x ≠ 0) = False := propext ⟨fun h => same h.1, False.elim⟩
    simp only [reduced]
    apply Evaluates.boolean_stop (value := .scalar (.bool false)) (middle := heap) (flag := false)
    · exact Evaluates.compare (Evaluates.lookup getX) (Evaluates.lookup getY)
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, same])
    · rfl
    · rfl

private theorem erased_value (items : List Nat) (index : Nat) (within : index ≤ items.length)
    (heap : Mutable.Heap) (address : Nat) (found : heap[address]? = some (.list (numbers items)))
    (env : HeapCalls.Env) (listName indexName : String)
    (getList : env listName = some (.ref address)) (getIndex : env indexName = some (number index)) :
    Evaluates program env (.call (.name "of_digits_le")
      [.call (.name "erase_nth") [.name listName, .name indexName]]) heap
      (number (Nat.ofDigits 10 (eraseNth items index))) (heap ++ erasedObjects items index) := by
  apply Evaluates.call (.cons (Evaluates.call
    (.cons (Evaluates.lookup getList) (.cons (Evaluates.lookup getIndex) .nil))
    (erase_nth.result items index within heap address found)) .nil)
  exact of_digits_result (eraseNth items index) _ (heap.length + 2) (by simp)

private theorem attempt_result (n d : Nat) (dn dd : List Nat) (i x j y : Nat)
    (withinI : i ≤ dn.length) (withinJ : j ≤ dd.length)
    (heap : Mutable.Heap) (dnAddress ddAddress : Nat)
    (foundN : heap[dnAddress]? = some (.list (numbers dn)))
    (foundD : heap[ddAddress]? = some (.list (numbers dd)))
    (env : HeapCalls.Env) (locals : RowLocals env n d dnAddress ddAddress i x)
    (getJ : env "j" = some (number j)) (getY : env "y" = some (number y)) :
    ∃ extra finalEnv, RowLocals finalEnv n d dnAddress ddAddress i x ∧
      Checked env innerCode heap finalEnv (heap ++ extra) (attempt n d dn dd i x j y) := by
  have condition := common_digit x y env heap locals.digit getY
  by_cases shared : x = y ∧ x ≠ 0
  · have conditionTrue := condition
    rw [show decide (x = y ∧ x ≠ 0) = true from decide_eq_true_iff.mpr shared] at conditionTrue
    let np := Nat.ofDigits 10 (eraseNth dn i)
    let dp := Nat.ofDigits 10 (eraseNth dd j)
    let middle := heap ++ erasedObjects dn i
    let final := middle ++ erasedObjects dd j
    let afterN := setLocal env "np" (number np)
    let afterD := setLocal afterN "dp" (number dp)
    have localsN : RowLocals afterN n d dnAddress ddAddress i x := locals.other "np" (number np) (by decide)
    have localsD : RowLocals afterD n d dnAddress ddAddress i x := localsN.other "dp" (number dp) (by decide)
    have nValue : Evaluates program env
        (.call (.name "of_digits_le") [.call (.name "erase_nth") [.name "dn", .name "i"]]) heap (number np) middle :=
      erased_value dn i withinI heap dnAddress foundN env "dn" "i" locals.numeratorDigits locals.index
    have dValue : Evaluates program afterN
        (.call (.name "of_digits_le") [.call (.name "erase_nth") [.name "dd", .name "j"]]) middle (number dp) final :=
      erased_value dd j withinJ middle ddAddress (found_append foundD _) afterN "dd" "j"
        localsN.denominatorDigits (by simpa [afterN, setLocal] using getJ)
    have compared : Evaluates program afterD
        (.compare (.binOp (.name "n") .mult (.name "dp"))
          [(.eq, .binOp (.name "d") .mult (.name "np"))]) final
        (.scalar (.bool (decide (n * dp = d * np)))) final := by
      apply Evaluates.compare (av := number (n * dp)) (bv := number (d * np))
        (middle := final) (afterRight := final)
      · exact Evaluates.binary (av := number n) (bv := number dp) (middle := final) (afterRight := final) (Evaluates.lookup localsD.numerator)
          (Evaluates.lookup (by simp [afterD, setLocal])) (by simp [Mutable.binary, scalarBinary, number])
      · exact Evaluates.binary (av := number d) (bv := number np) (middle := final) (afterRight := final) (Evaluates.lookup localsD.denominator)
          (Evaluates.lookup (by simp [afterD, afterN, setLocal])) (by simp [Mutable.binary, scalarBinary, number])
      · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
        simp only [← Int.natCast_mul, Int.ofNat_inj]
    by_cases equal : n * dp = d * np
    · refine ⟨erasedObjects dn i ++ erasedObjects dd j, afterD, localsD, ?_⟩
      have accepted : attempt n d dn dd i x j y = true := by
        rw [attempt, if_pos shared]
        exact decide_eq_true_iff.mpr equal
      rw [accepted]
      change ∀ following, BlockReturns program env (innerCode ++ following) heap (.scalar (.bool true)) _
      intro following
      apply BlockReturns.branch (flag := true) conditionTrue rfl
      apply BlockReturns.assign nValue
      apply BlockReturns.assign dValue
      apply BlockReturns.branch (flag := true) (by simpa [equal] using compared) rfl
      simpa only [final, middle, List.append_assoc] using
        (BlockReturns.return_value (Evaluates.constant (value := .bool true)) :
          BlockReturns program afterD (.return (.constant (.bool true)) :: following)
            final (.scalar (.bool true)) final)
    · refine ⟨erasedObjects dn i ++ erasedObjects dd j, afterD, localsD, ?_⟩
      have accepted : attempt n d dn dd i x j y = false := by
        rw [attempt, if_pos shared]
        exact decide_eq_false_iff_not.mpr equal
      rw [accepted]
      change BlockContinues program env innerCode heap afterD _
      apply BlockContinues.branch (flag := true) conditionTrue rfl
      apply (BlockContinues.assign nValue).append
      apply (BlockContinues.assign dValue).append
      apply BlockContinues.branch (flag := false) (by simpa [equal] using compared) rfl
      simpa only [final, middle, List.append_assoc] using (BlockContinues.nil :
        BlockContinues program afterD [] final afterD final)
  · refine ⟨[], env, locals, ?_⟩
    rw [attempt, if_neg shared]
    change BlockContinues program env innerCode heap env (heap ++ [])
    simp only [List.append_nil]
    rw [show decide (x = y ∧ x ≠ 0) = false from decide_eq_false_iff_not.mpr shared] at condition
    exact BlockContinues.branch (flag := false) condition rfl BlockContinues.nil

private def rowChecks (n d : Nat) (dn dd : List Nat) (i x position : Nat) : List Nat → Bool
  | [] => false
  | y :: tail => attempt n d dn dd i x position y || rowChecks n d dn dd i x (position + 1) tail

private def allChecks (n d : Nat) (dn dd : List Nat) (position : Nat) : List Nat → Bool
  | [] => false
  | x :: tail => rowChecks n d dn dd position x 0 dd || allChecks n d dn dd (position + 1) tail

private theorem Checked.enumerate_step
    (sequence : Mutable.sequence (sequenceValue source) heap = some (.ok items, heap))
    (item : items[position]? = some value)
    (rest : Checked (setLocal (setLocal env index (.scalar (.int counter))) name value)
      (body ++ [Calls.loopContinuation body
        (.enumerateStepLoop index name source (position + 1) (counter + 1) body otherwise)])
      heap finalEnv finalHeap accepted) :
    Checked env [.enumerateStepLoop index name source position counter body otherwise]
      heap finalEnv finalHeap accepted := by
  cases accepted with
  | false => exact BlockContinues.enumerate_step sequence item rest
  | true =>
      intro following
      apply returns_enumerate_step sequence item
      simpa only [List.append_assoc, List.singleton_append] using rest following

private theorem Checked.for_enumerate
    (iterable : Evaluates program env expression heap source middle)
    (sequence : Mutable.sequence source middle = some (.ok items, middle))
    (rest : Checked env [.enumerateStepLoop index name (sequenceSource source) 0 0 body otherwise]
      middle finalEnv finalHeap accepted) :
    Checked env [.forIn (.tuple [.name index, .name name]) (.call (.name "enumerate") [expression]) body otherwise]
      heap finalEnv finalHeap accepted := by
  cases accepted with
  | false => exact BlockContinues.for_enumerate iterable sequence rest
  | true => exact fun following => returns_for_enumerate iterable sequence (rest following)

private theorem inner_scan (n d : Nat) (dn dd : List Nat) (i x : Nat) (withinI : i ≤ dn.length)
    (remaining : List Nat) (position : Nat) (suffix : dd.drop position = remaining)
    (heap : Mutable.Heap) (dnAddress ddAddress : Nat)
    (foundN : heap[dnAddress]? = some (.list (numbers dn)))
    (foundD : heap[ddAddress]? = some (.list (numbers dd)))
    (env : HeapCalls.Env) (locals : RowLocals env n d dnAddress ddAddress i x) :
    ∃ extra finalEnv, RowLocals finalEnv n d dnAddress ddAddress i x ∧
      Checked env [.enumerateStepLoop "j" "y" (.ref ddAddress) position position innerCode []]
        heap finalEnv (heap ++ extra) (rowChecks n d dn dd i x position remaining) := by
  induction remaining generalizing position heap env with
  | nil =>
      refine ⟨[], env, locals, ?_⟩
      simp only [rowChecks, Checked, List.append_nil]
      apply BlockContinues.enumerate_done (items := numbers dd)
        (by simp [sequenceValue, Mutable.sequence, foundD])
      · have missing : dd[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := dd) (i := position)).symm
        simp [numbers, missing]
      · exact BlockContinues.nil
  | cons y tail ih =>
      have item : dd[position]? = some y := by
        simpa [suffix] using (List.head?_drop (l := dd) (i := position)).symm
      let bound := setLocal (setLocal env "j" (number position)) "y" (number y)
      have boundLocals : RowLocals bound n d dnAddress ddAddress i x :=
        (locals.other "j" (number position) (by decide)).other "y" (number y) (by decide)
      obtain ⟨extra, middleEnv, middleLocals, tested⟩ := attempt_result n d dn dd i x position y
        withinI (by have := (List.getElem?_eq_some_iff.mp item).1; omega)
        heap dnAddress ddAddress foundN foundD bound boundLocals
        (by simp [bound, setLocal]) (by simp [bound, setLocal])
      cases accepted : attempt n d dn dd i x position y with
      | true =>
          refine ⟨extra, middleEnv, middleLocals, ?_⟩
          simp only [rowChecks, accepted, Bool.true_or, Checked]
          intro following
          apply returns_enumerate_step (items := numbers dd) (value := number y)
            (by simp [sequenceValue, Mutable.sequence, foundD]) (by simp [numbers, item])
          exact (show ∀ following, BlockReturns program bound (innerCode ++ following) heap
            (.scalar (.bool true)) (heap ++ extra) from by simpa [Checked, accepted] using tested) _
      | false =>
          obtain ⟨more, finalEnv, finalLocals, rest⟩ := ih (position + 1)
            (by simp [List.drop_add_one_eq_tail_drop, suffix]) (heap ++ extra)
            (found_append foundN extra) (found_append foundD extra) middleEnv middleLocals
          refine ⟨extra ++ more, finalEnv, finalLocals, ?_⟩
          simp only [rowChecks, accepted, Bool.false_or]
          apply Checked.enumerate_step (items := numbers dd) (value := number y)
            (by simp [sequenceValue, Mutable.sequence, foundD]) (by simp [numbers, item])
          have continued : BlockContinues program bound innerCode heap middleEnv (heap ++ extra) :=
            by simpa [Checked, accepted] using tested
          have joined := Checked.prepend continued rest
          simpa only [Calls.loopContinuation, show Calls.loopControl innerCode = false from rfl,
            ↓reduceIte, Int.natCast_add, Int.natCast_one, List.append_assoc] using joined

private theorem outer_scan (n d : Nat) (dn dd : List Nat)
    (remaining : List Nat) (position : Nat) (suffix : dn.drop position = remaining)
    (heap : Mutable.Heap) (dnAddress ddAddress : Nat)
    (foundN : heap[dnAddress]? = some (.list (numbers dn)))
    (foundD : heap[ddAddress]? = some (.list (numbers dd)))
    (env : HeapCalls.Env) (locals : LoopLocals env n d dnAddress ddAddress) :
    ∃ extra finalEnv, LoopLocals finalEnv n d dnAddress ddAddress ∧
      Checked env [.enumerateStepLoop "i" "x" (.ref dnAddress) position position outerCode []]
        heap finalEnv (heap ++ extra) (allChecks n d dn dd position remaining) := by
  induction remaining generalizing position heap env with
  | nil =>
      refine ⟨[], env, locals, ?_⟩
      simp only [allChecks, Checked, List.append_nil]
      apply BlockContinues.enumerate_done (items := numbers dn)
        (by simp [sequenceValue, Mutable.sequence, foundN])
      · have missing : dn[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := dn) (i := position)).symm
        simp [numbers, missing]
      · exact BlockContinues.nil
  | cons x tail ih =>
      have item : dn[position]? = some x := by
        simpa [suffix] using (List.head?_drop (l := dn) (i := position)).symm
      let bound := setLocal (setLocal env "i" (number position)) "x" (number x)
      have boundLocals : RowLocals bound n d dnAddress ddAddress position x :=
        ⟨(locals.other "i" (number position) (by decide)).other "x" (number x) (by decide),
          by simp [bound, setLocal], by simp [bound, setLocal]⟩
      obtain ⟨extra, middleEnv, middleLocals, inner⟩ := inner_scan n d dn dd position x
        (by have := (List.getElem?_eq_some_iff.mp item).1; omega) dd 0 rfl
        heap dnAddress ddAddress foundN foundD bound boundLocals
      have tested : Checked bound outerCode heap middleEnv (heap ++ extra)
          (rowChecks n d dn dd position x 0 dd) :=
        Checked.for_enumerate (items := numbers dd) (Evaluates.lookup boundLocals.denominatorDigits)
          (by simp [Mutable.sequence, foundD]) inner
      cases accepted : rowChecks n d dn dd position x 0 dd with
      | true =>
          refine ⟨extra, middleEnv, middleLocals.toLoopLocals, ?_⟩
          simp only [allChecks, accepted, Bool.true_or, Checked]
          intro following
          apply returns_enumerate_step (items := numbers dn) (value := number x)
            (by simp [sequenceValue, Mutable.sequence, foundN]) (by simp [numbers, item])
          exact (show ∀ following, BlockReturns program bound (outerCode ++ following) heap
            (.scalar (.bool true)) (heap ++ extra) from by simpa [Checked, accepted] using tested) _
      | false =>
          obtain ⟨more, finalEnv, finalLocals, rest⟩ := ih (position + 1)
            (by simp [List.drop_add_one_eq_tail_drop, suffix]) (heap ++ extra)
            (found_append foundN extra) (found_append foundD extra) middleEnv middleLocals.toLoopLocals
          refine ⟨extra ++ more, finalEnv, finalLocals, ?_⟩
          simp only [allChecks, accepted, Bool.false_or]
          apply Checked.enumerate_step (items := numbers dn) (value := number x)
            (by simp [sequenceValue, Mutable.sequence, foundN]) (by simp [numbers, item])
          have continued : BlockContinues program bound outerCode heap middleEnv (heap ++ extra) :=
            by simpa [Checked, accepted] using tested
          have joined := Checked.prepend continued rest
          simpa only [Calls.loopContinuation, show Calls.loopControl outerCode = false from rfl,
            ↓reduceIte, Int.natCast_add, Int.natCast_one, List.append_assoc] using joined

private def validDigits (n d : Nat) : Prop :=
  (Nat.digits 10 n).length = (Nat.digits 10 d).length ∧ 2 ≤ (Nat.digits 10 n).length ∧ n < d
private instance (n d : Nat) : Decidable (validDigits n d) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private theorem checked_predicate (n d : Nat) (smallN : n < 100) (smallD : d < 100) :
    isCurious n d = if validDigits n d then allChecks n d (Nat.digits 10 n) (Nat.digits 10 d) 0 (Nat.digits 10 n) else false := by
  by_cases valid : validDigits n d
  · have bounds : 10 ≤ n ∧ 10 ≤ d ∧ n < d := (decimal_guard n d smallN smallD).mp valid
    have digitsN : Nat.digits 10 n = [n % 10, n / 10] := by
      simp [decimal_digits n smallN, show n ≠ 0 by omega, show ¬ n < 10 by omega]
    have digitsD : Nat.digits 10 d = [d % 10, d / 10] := by
      simp [decimal_digits d smallD, show d ≠ 0 by omega, show ¬ d < 10 by omega]
    simp only [isCurious, show (Nat.digits 10 n).length = (Nat.digits 10 d).length ∧
      2 ≤ (Nat.digits 10 n).length ∧ n < d from valid, valid, ↓reduceIte]
    rw [digitsN, digitsD]
    simp [allChecks, rowChecks, attempt, eraseNth, List.range_succ, Bool.or_assoc,
      show ¬ n < 10 by omega]
  · simp only [isCurious, show ¬ ((Nat.digits 10 n).length = (Nat.digits 10 d).length ∧
      2 ≤ (Nat.digits 10 n).length ∧ n < d) from valid, valid, ↓reduceIte]

private abbrev guardExpression : Expr := .boolOp .and
  [.compare (.builtinCall .len [.name "dn"]) [(.eq, .builtinCall .len [.name "dd"])],
    .compare (.constant (.int 2)) [(.ltE, .builtinCall .len [.name "dn"])],
    .compare (.name "n") [(.lt, .name "d")]]

private theorem guard_result (n d : Nat) (dn dd : List Nat) (heap : Mutable.Heap)
    (dnAddress ddAddress : Nat) (env : HeapCalls.Env) (locals : LoopLocals env n d dnAddress ddAddress)
    (foundN : heap[dnAddress]? = some (.list (numbers dn)))
    (foundD : heap[ddAddress]? = some (.list (numbers dd))) :
    Evaluates program env guardExpression heap
      (.scalar (.bool (decide (dn.length = dd.length ∧ 2 ≤ dn.length ∧ n < d)))) heap := by
  have lenN : Evaluates program env (.builtinCall .len [.name "dn"]) heap (number dn.length) heap :=
    Evaluates.builtin (.cons (Evaluates.lookup locals.numeratorDigits) .nil)
      (by simp [primitive, Mutable.length, foundN, numbers])
  have lenD : Evaluates program env (.builtinCall .len [.name "dd"]) heap (number dd.length) heap :=
    Evaluates.builtin (.cons (Evaluates.lookup locals.denominatorDigits) .nil)
      (by simp [primitive, Mutable.length, foundD, numbers])
  have first : Evaluates program env (.compare (.builtinCall .len [.name "dn"])
      [(.eq, .builtinCall .len [.name "dd"])]) heap (.scalar (.bool (decide (dn.length = dd.length)))) heap :=
    Evaluates.compare lenN lenD (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  have second : Evaluates program env (.compare (.constant (.int 2))
      [(.ltE, .builtinCall .len [.name "dn"])]) heap (.scalar (.bool (decide (2 ≤ dn.length)))) heap :=
    Evaluates.compare Evaluates.constant lenN (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  have third : Evaluates program env (.compare (.name "n") [(.lt, .name "d")]) heap
      (.scalar (.bool (decide (n < d)))) heap :=
    Evaluates.compare (Evaluates.lookup locals.numerator) (Evaluates.lookup locals.denominator)
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  by_cases same : dn.length = dd.length
  · have reduced : (dn.length = dd.length ∧ 2 ≤ dn.length ∧ n < d) = (2 ≤ dn.length ∧ n < d) :=
      propext ⟨And.right, fun h => ⟨same, h⟩⟩
    simp only [reduced]
    apply Evaluates.boolean_next (flag := true) (by simpa [same] using first) rfl rfl
    by_cases long : 2 ≤ dn.length
    · have reduced : (2 ≤ dn.length ∧ n < d) = (n < d) := propext ⟨And.right, fun h => ⟨long, h⟩⟩
      simp only [reduced]
      apply Evaluates.boolean_next (flag := true) (by simpa [long] using second) rfl rfl
      exact Evaluates.boolean_last third rfl
    · have reduced : (2 ≤ dn.length ∧ n < d) = False := propext ⟨fun h => long h.1, False.elim⟩
      simp only [reduced]
      exact Evaluates.boolean_stop (flag := false) (by simpa [long] using second) rfl rfl
  · have reduced : (dn.length = dd.length ∧ 2 ≤ dn.length ∧ n < d) = False :=
      propext ⟨fun h => same h.1, False.elim⟩
    simp only [reduced]
    exact Evaluates.boolean_stop (flag := false) (by simpa [same] using first) rfl rfl

/-- Bounded reference predicate execution, with every input heap object preserved. -/
theorem is_curious.result (n d : Nat) (smallN : n < 100) (smallD : d < 100) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "is_curious" [number n, number d] heap
      (.scalar (.bool (isCurious n d))) (heap ++ extra) := by
  let dn := Nat.digits 10 n
  let dd := Nat.digits 10 d
  let first := heap ++ [Mutable.Object.list (numbers dn)]
  let second := first ++ [Mutable.Object.list (numbers dd)]
  let allocated : Mutable.Heap := [.list (numbers dn), .list (numbers dd),
    .tuple [.ref heap.length, .ref (heap.length + 1)]]
  let readyHeap := heap ++ allocated
  let args := ((findFunctionIn program.body "is_curious").getD ([], [])).1
  let body := ((findFunctionIn program.body "is_curious").getD ([], [])).2
  let initial := functionEnv args body [number n, number d] []
  let ready := assignNames initial ["dn", "dd"] [.ref heap.length, .ref (heap.length + 1)]
  have locals : LoopLocals ready n d heap.length (heap.length + 1) := by
    constructor <;> rfl
  have foundN : readyHeap[heap.length]? = some (.list (numbers dn)) := by simp [readyHeap, allocated]
  have foundD : readyHeap[heap.length + 1]? = some (.list (numbers dd)) := by simp [readyHeap, allocated]
  have digitsN : Evaluates program initial (.call (.name "digits_le") [.name "n"])
      heap (.ref heap.length) first :=
    Evaluates.call (.cons (Evaluates.lookup rfl) .nil) ((common.digits_le.decimal n heap).extend common_extension)
  have digitsD : Evaluates program initial (.call (.name "digits_le") [.name "d"])
      first (.ref first.length) second :=
    Evaluates.call (.cons (Evaluates.lookup rfl) .nil) ((common.digits_le.decimal d first).extend common_extension)
  have pair : Evaluates program initial
      (.tuple [.call (.name "digits_le") [.name "n"], .call (.name "digits_le") [.name "d"]])
      heap (.ref (heap.length + 2)) readyHeap := by
    simpa [first, second, readyHeap, allocated, List.append_assoc] using
      Evaluates.tuple (.cons digitsN (.cons digitsD .nil)) (by simp)
  have tested := guard_result n d dn dd readyHeap heap.length (heap.length + 1) ready locals foundN foundD
  have negative : Evaluates program ready (.unaryOp .not guardExpression) readyHeap
      (.scalar (.bool (!decide (validDigits n d)))) readyHeap := by
    apply Evaluates.unary tested
    rfl
  by_cases valid : validDigits n d
  · obtain ⟨extra, finalEnv, _, checked⟩ := outer_scan n d dn dd dn 0 rfl
      readyHeap heap.length (heap.length + 1) foundN foundD ready locals
    have scanned : Checked ready
        [.forIn (.tuple [.name "i", .name "x"]) (.call (.name "enumerate") [.name "dn"]) outerCode []]
        readyHeap finalEnv (readyHeap ++ extra) (allChecks n d dn dd 0 dn) :=
      Checked.for_enumerate (items := numbers dn) (Evaluates.lookup locals.numeratorDigits)
        (by simp [Mutable.sequence, foundN]) checked
    refine ⟨allocated ++ extra, ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.unpack (items := [.ref heap.length, .ref (heap.length + 1)])
      (afterUnpack := readyHeap) rfl pair
      (by simp [Mutable.sequence, readyHeap, allocated]) rfl
    apply BlockReturns.branch (flag := false) (by simpa [valid] using negative) rfl
    cases accepted : allChecks n d dn dd 0 dn with
    | true =>
        have returned := (show ∀ following, BlockReturns program ready
          ([.forIn (.tuple [.name "i", .name "x"]) (.call (.name "enumerate") [.name "dn"]) outerCode []] ++ following)
          readyHeap (.scalar (.bool true)) (readyHeap ++ extra) from by simpa [Checked, accepted] using scanned)
          [.return (.constant (.bool false))]
        dsimp only [dn, dd] at accepted
        simpa [checked_predicate n d smallN smallD, valid, accepted, readyHeap, List.append_assoc] using returned
    | false =>
        have continued : BlockContinues program ready
            [.forIn (.tuple [.name "i", .name "x"]) (.call (.name "enumerate") [.name "dn"]) outerCode []]
            readyHeap finalEnv (readyHeap ++ extra) := by simpa [Checked, accepted] using scanned
        have returned := continued.returns (BlockReturns.return_value
          (Evaluates.constant (value := .bool false)) :
          BlockReturns program finalEnv [.return (.constant (.bool false))]
            (readyHeap ++ extra) (.scalar (.bool false)) (readyHeap ++ extra))
        dsimp only [dn, dd] at accepted
        simpa [checked_predicate n d smallN smallD, valid, accepted, readyHeap, List.append_assoc] using returned
  · refine ⟨allocated, ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.unpack (items := [.ref heap.length, .ref (heap.length + 1)])
      (afterUnpack := readyHeap) rfl pair
      (by simp [Mutable.sequence, readyHeap, allocated]) rfl
    apply BlockReturns.branch (flag := true) (by simpa [valid] using negative) rfl
    simpa only [checked_predicate n d smallN smallD, valid, ↓reduceIte] using
      (BlockReturns.return_value (Evaluates.constant (value := .bool false)) :
        BlockReturns program ready (.return (.constant (.bool false)) :: curiousCode.drop 2)
          readyHeap (.scalar (.bool false)) readyHeap)

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

/-- Every collected pair has its own tuple, following the private result list. -/
def Rows (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat) (pairs : List (Nat × Nat)) : Prop :=
  List.Forall₂ (fun address pair => collector < address ∧
    heap[address]? = some (.tuple [number pair.1, number pair.2])) addresses pairs

private theorem Rows.preserve {heap finalHeap : Mutable.Heap} {collector : Nat}
    {addresses : List Nat} {pairs : List (Nat × Nat)} (rows : Rows heap collector addresses pairs)
    (preserved : Preserves heap finalHeap collector) : Rows finalHeap collector addresses pairs := by
  induction rows with
  | nil => exact .nil
  | @cons address pair addresses pairs first rest ih =>
      exact .cons ⟨first.1, preserved address _ (by omega) first.2⟩ ih

private abbrev candidateBody (collector : Nat) : List Stmt :=
  [.ifThen (.call (.name "is_curious") [.name "n", .name "d"])
    [.comprehensionAppend collector (.tuple [.name "n", .name "d"])] []]

private def rowSlice (n first count : Nat) : List (Nat × Nat) :=
  ((List.range' first count).filter (isCurious n)).map (fun d => (n, d))

private theorem collect_row (n : Nat) (smallN : n < 100) (first count : Nat) (bound : first + count = 100)
    (before : List (Nat × Nat)) (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat)
    (found : heap[collector]? = some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses before) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) :
    ∃ finalHeap finalEnv finalAddresses,
      BlockContinues program env [.rangeStepLoop "d" first 100 1 (candidateBody collector) []]
        heap finalEnv finalHeap ∧
      finalHeap[collector]? = some (.list (finalAddresses.map Mutable.Value.ref)) ∧
      Rows finalHeap collector finalAddresses (before ++ rowSlice n first count) ∧
      finalEnv "n" = some (number n) := by
  induction count generalizing first before heap addresses env with
  | zero =>
      refine ⟨heap, env, addresses, ?_, found, ?_, getN⟩
      · exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) BlockContinues.nil
      · simpa [rowSlice] using rows
  | succ count ih =>
      let boundEnv := setLocal env "d" (number first)
      have boundN : boundEnv "n" = some (number n) := by simpa [boundEnv, setLocal] using getN
      obtain ⟨extra, predicate⟩ := is_curious.result n first smallN (by omega) heap
      let middle := heap ++ extra
      have tested : Evaluates program boundEnv (.call (.name "is_curious") [.name "n", .name "d"])
          heap (.scalar (.bool (isCurious n first))) middle :=
        Evaluates.call (.cons (Evaluates.lookup boundN) (.cons (Evaluates.lookup (by simp [boundEnv, setLocal])) .nil)) predicate
      cases accepted : isCurious n first with
      | false =>
          obtain ⟨finalHeap, finalEnv, finalAddresses, rest, finalFound, finalRows, finalN⟩ :=
            ih (first + 1) (by omega) before middle addresses (found_append found extra)
              (rows.preserve (appended heap extra collector)) boundEnv boundN
          refine ⟨finalHeap, finalEnv, finalAddresses, ?_, finalFound, ?_, finalN⟩
          · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
            have skipped : BlockContinues program boundEnv (candidateBody collector) heap boundEnv middle :=
              BlockContinues.branch (flag := false) (by simpa [accepted] using tested) rfl BlockContinues.nil
            simpa only [Calls.loopContinuation, show Calls.loopControl (candidateBody collector) = false from rfl,
              ↓reduceIte, Int.natCast_add, Int.natCast_one] using skipped.append rest
          · simpa [rowSlice, List.range'_succ, accepted] using finalRows
      | true =>
          let nextAddresses := addresses ++ [middle.length]
          let nextHeap := (middle ++ [Mutable.Object.tuple [number n, number first]]).set collector
            (.list (nextAddresses.map Mutable.Value.ref))
          have inside : collector < middle.length := by
            have := (List.getElem?_eq_some_iff.mp found).1
            simp only [middle, List.length_append]
            omega
          have pair : Evaluates program boundEnv (.tuple [.name "n", .name "d"])
              middle (.ref middle.length) (middle ++ [.tuple [number n, number first]]) :=
            Evaluates.tuple (.cons (Evaluates.lookup boundN)
              (.cons (Evaluates.lookup (by simp [boundEnv, setLocal])) .nil)) (by simp)
          have emitted : BlockContinues program boundEnv (candidateBody collector) heap boundEnv nextHeap := by
            apply BlockContinues.branch (flag := true) (by simpa [accepted] using tested) rfl
            simpa [nextHeap, nextAddresses] using BlockContinues.comprehension_append pair
              (found_append (found_append found extra) [.tuple [number n, number first]])
          have nextFound : nextHeap[collector]? = some (.list (nextAddresses.map Mutable.Value.ref)) := by
            apply List.getElem?_set_self
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          have preserved : Preserves heap nextHeap collector :=
            (appended heap extra collector).trans
              ((appended middle [.tuple [number n, number first]] collector).trans
                (updated _ collector _))
          have fresh : collector < middle.length ∧ nextHeap[middle.length]? =
              some (.tuple [number n, number first]) := by
            refine ⟨inside, ?_⟩
            change ((middle ++ [Mutable.Object.tuple [number n, number first]]).set collector _)[middle.length]? = _
            rw [List.getElem?_set_ne (by omega : collector ≠ middle.length)]
            simp
          have nextRows : Rows nextHeap collector nextAddresses (before ++ [(n, first)]) :=
            List.rel_append (rows.preserve preserved) (.cons fresh .nil)
          obtain ⟨finalHeap, finalEnv, finalAddresses, rest, finalFound, finalRows, finalN⟩ :=
            ih (first + 1) (by omega) (before ++ [(n, first)]) nextHeap nextAddresses
              nextFound nextRows boundEnv boundN
          refine ⟨finalHeap, finalEnv, finalAddresses, ?_, finalFound, ?_, finalN⟩
          · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
            simpa only [Calls.loopContinuation, show Calls.loopControl (candidateBody collector) = false from rfl,
              ↓reduceIte, Int.natCast_add, Int.natCast_one] using emitted.append rest
          · simpa [rowSlice, List.range'_succ, accepted, List.append_assoc] using finalRows

private abbrev collectionBody (collector : Nat) : List Stmt :=
  [.forIn (.name "d") (.call (.name "range") [.constant (.int 100)]) (candidateBody collector) []]

private theorem collect_all (first count : Nat) (bound : first + count = 100)
    (before : List (Nat × Nat)) (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat)
    (found : heap[collector]? = some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses before) (env : HeapCalls.Env) :
    ∃ finalHeap finalEnv finalAddresses,
      BlockContinues program env [.rangeStepLoop "n" first 100 1 (collectionBody collector) []]
        heap finalEnv finalHeap ∧
      finalHeap[collector]? = some (.list (finalAddresses.map Mutable.Value.ref)) ∧
      Rows finalHeap collector finalAddresses
        (before ++ (List.range' first count).flatMap ProjectEulerStatements.DigitCancellingFractions.referenceRow) := by
  induction count generalizing first before heap addresses env with
  | zero =>
      refine ⟨heap, env, addresses, ?_, found, ?_⟩
      · exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) BlockContinues.nil
      · simpa using rows
  | succ count ih =>
      let boundEnv := setLocal env "n" (number first)
      obtain ⟨middle, middleEnv, middleAddresses, inner, middleFound, middleRows, _⟩ :=
        collect_row first (by omega) 0 100 rfl before heap collector addresses found rows boundEnv
          (by simp [boundEnv, setLocal])
      have scanned : BlockContinues program boundEnv (collectionBody collector) heap middleEnv middle :=
        BlockContinues.for_range (.cons Evaluates.constant .nil) rfl inner
      have accumulated : before ++ rowSlice first 0 100 =
          before ++ ProjectEulerStatements.DigitCancellingFractions.referenceRow first := rfl
      rw [accumulated] at middleRows
      obtain ⟨finalHeap, finalEnv, finalAddresses, rest, finalFound, finalRows⟩ :=
        ih (first + 1) (by omega)
          (before ++ ProjectEulerStatements.DigitCancellingFractions.referenceRow first)
          middle middleAddresses middleFound middleRows middleEnv
      refine ⟨finalHeap, finalEnv, finalAddresses, ?_, finalFound, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, show Calls.loopControl (collectionBody collector) = false from rfl,
          ↓reduceIte, Int.natCast_add, Int.natCast_one] using scanned.append rest
      · simpa [List.range'_succ, List.append_assoc] using finalRows

/-- The comprehension retains the exact tuple identities emitted by its source. -/
theorem curious_fractions.result (heap : Mutable.Heap) :
    ∃ finalHeap addresses, ReturnsValue program "curious_fractions" [] heap (.ref heap.length) finalHeap ∧
      finalHeap[heap.length]? = some (.list (addresses.map Mutable.Value.ref)) ∧
      Rows finalHeap heap.length addresses curiousFractions := by
  let args := ((findFunctionIn program.body "curious_fractions").getD ([], [])).1
  let body := ((findFunctionIn program.body "curious_fractions").getD ([], [])).2
  let initial := functionEnv args body [] []
  let generators : List (String × Expr × List Expr) :=
    [("n", .call (.name "range") [.constant (.int 100)], []),
      ("d", .call (.name "range") [.constant (.int 100)],
        [.call (.name "is_curious") [.name "n", .name "d"]])]
  obtain ⟨finalHeap, finalEnv, addresses, collected, found, rows⟩ :=
    collect_all 0 100 rfl [] (heap ++ [.list []]) heap.length [] (by simp) .nil
      (comprehensionEnv initial generators)
  refine ⟨finalHeap, addresses, ?_, found, ?_⟩
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    exact Evaluates.list_comp_range (values := [number 100]) (middle := heap)
      (finalEnv := finalEnv) (.cons Evaluates.constant .nil) rfl collected
  · simpa only [ProjectEulerStatements.DigitCancellingFractions.curiousFractions_eq_rows,
      List.nil_append, List.range_eq_range'] using rows

private theorem Rows.at {heap : Mutable.Heap} {collector : Nat} {addresses : List Nat}
    {pairs : List (Nat × Nat)} {pair : Nat × Nat} (rows : Rows heap collector addresses pairs)
    (position : Nat) (item : pairs[position]? = some pair) :
    ∃ address, addresses[position]? = some address ∧
      heap[address]? = some (.tuple [number pair.1, number pair.2]) := by
  induction rows generalizing position with
  | nil => simp at item
  | @cons address head addresses pairs first rest ih =>
      cases position with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at item
          subst pair
          exact ⟨address, rfl, first.2⟩
      | succ position =>
          exact ih position (by simpa using item)

private abbrev multiplicationBody : List Stmt :=
  [.augAssign (.name "pn") .mult (.name "n"), .augAssign (.name "pd") .mult (.name "d")]

private def productFrom (items : List (Nat × Nat)) (pn pd : Nat) : Nat × Nat :=
  items.foldl (fun acc item => (acc.1 * item.1, acc.2 * item.2)) (pn, pd)

private theorem multiplication_loop (pairs remaining : List (Nat × Nat)) (position : Nat)
    (suffix : pairs.drop position = remaining) (heap : Mutable.Heap) (collector : Nat) (addresses : List Nat)
    (found : heap[collector]? = some (.list (addresses.map Mutable.Value.ref)))
    (rows : Rows heap collector addresses pairs) (env : HeapCalls.Env) (pn pd : Nat)
    (getN : env "pn" = some (number pn)) (getD : env "pd" = some (number pd)) :
    ∃ finalEnv, BlockContinues program env
      [.unpackStepLoop ["n", "d"] (.ref collector) position multiplicationBody []] heap finalEnv heap ∧
      finalEnv "pn" = some (number (productFrom remaining pn pd).1) ∧
      finalEnv "pd" = some (number (productFrom remaining pn pd).2) := by
  induction remaining generalizing position env pn pd with
  | nil =>
      refine ⟨env, ?_, getN, getD⟩
      apply BlockContinues.unpack_done (source := .ref collector) (items := addresses.map Mutable.Value.ref)
        (by simp [sequenceValue, Mutable.sequence, found])
      · have missing : pairs[position]? = none := by
          simpa [suffix] using (List.head?_drop (l := pairs) (i := position)).symm
        have length := List.Forall₂.length_eq rows
        have outside := List.getElem?_eq_none_iff.mp missing
        simp [List.getElem?_eq_none (by omega : addresses.length ≤ position)]
      · exact BlockContinues.nil
  | cons pair remaining ih =>
      have item : pairs[position]? = some pair := by
        simpa [suffix] using (List.head?_drop (l := pairs) (i := position)).symm
      obtain ⟨address, selected, fields⟩ := rows.at position item
      let bound := assignNames env ["n", "d"] [number pair.1, number pair.2]
      let afterN := setLocal bound "pn" (number (pn * pair.1))
      let afterD := setLocal afterN "pd" (number (pd * pair.2))
      have multiplyN : BlockContinues program bound [multiplicationBody[0]'(by decide)] heap afterN heap := by
        apply BlockContinues.augAssign (left := number pn) (right := number pair.1)
          (value := number (pn * pair.1)) (middle := heap) (finalHeap := heap)
        · simpa [bound, assignNames, setLocal] using getN
        · exact Evaluates.lookup (by simp [bound, assignNames, setLocal])
        · simp [HeapCalls.inplace, Mutable.binary, scalarBinary, number]
      have multiplyD : BlockContinues program afterN [multiplicationBody[1]'(by decide)] heap afterD heap := by
        apply BlockContinues.augAssign (left := number pd) (right := number pair.2)
          (value := number (pd * pair.2)) (middle := heap) (finalHeap := heap)
        · simpa [afterN, bound, assignNames, setLocal] using getD
        · exact Evaluates.lookup (by simp [afterN, bound, assignNames, setLocal])
        · simp [HeapCalls.inplace, Mutable.binary, scalarBinary, number]
      obtain ⟨finalEnv, rest, finalN, finalD⟩ := ih (position + 1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) afterD (pn * pair.1) (pd * pair.2)
        (by simp [afterD, afterN, setLocal]) (by simp [afterD, setLocal])
      refine ⟨finalEnv, ?_, finalN, finalD⟩
      apply BlockContinues.unpack_step (source := .ref collector) (items := addresses.map Mutable.Value.ref)
        (value := .ref address) (values := [number pair.1, number pair.2])
        (by simp [sequenceValue, Mutable.sequence, found]) (by simp [selected])
        (by simp [Mutable.sequence, fields]) rfl
      simpa only [Calls.loopContinuation, show Calls.loopControl multiplicationBody = false from rfl,
        ↓reduceIte] using multiplyN.append (multiplyD.append rest)

/-- The complete reference program returns the certified reduced denominator. -/
theorem naive.result (heap : Mutable.Heap) :
    ∃ finalHeap, ReturnsValue program "naive" [] heap (number ProjectEulerStatements.P33.naive) finalHeap := by
  rw [ProjectEulerStatements.DigitCancellingFractions.reference_value]
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let body := ((findFunctionIn program.body "naive").getD ([], [])).2
  let initial := functionEnv args body [] []
  let ready := assignNames initial ["pn", "pd"] [number 1, number 1]
  let readyHeap := heap ++ [Mutable.Object.tuple [number 1, number 1]]
  obtain ⟨finalHeap, addresses, collected, found, rows⟩ := curious_fractions.result readyHeap
  rw [ProjectEulerStatements.DigitCancellingFractions.reference_fractions] at rows
  obtain ⟨finalEnv, multiplied, finalN, finalD⟩ := multiplication_loop
    ProjectEulerStatements.DigitCancellingFractions.fractions ProjectEulerStatements.DigitCancellingFractions.fractions
    0 rfl finalHeap readyHeap.length addresses found rows ready 1 1 rfl rfl
  change finalEnv "pn" = some (number 387296) at finalN
  change finalEnv "pd" = some (number 38729600) at finalD
  have evaluated : Evaluates program ready (.call (.name "curious_fractions") []) readyHeap
      (.ref readyHeap.length) finalHeap := Evaluates.call .nil collected
  have loop : BlockContinues program ready
      [.forIn (.tuple [.name "n", .name "d"]) (.call (.name "curious_fractions") []) multiplicationBody []]
      readyHeap finalEnv finalHeap :=
    BlockContinues.for_unpack (items := addresses.map Mutable.Value.ref) (by intros; simp) rfl evaluated (by simp [Mutable.sequence, found]) multiplied
  refine ⟨finalHeap, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.unpack (items := [number 1, number 1]) (afterUnpack := readyHeap) rfl
    (Evaluates.tuple (.cons Evaluates.constant (.cons Evaluates.constant .nil)) (by simp))
    (by simp [Mutable.sequence, readyHeap, number]) rfl
  apply loop.returns
  apply BlockReturns.return_value
  apply Evaluates.binary (av := number 38729600) (bv := number 387296)
    (middle := finalHeap) (afterRight := finalHeap)
  · exact Evaluates.lookup finalD
  · apply Evaluates.library_call (.cons (Evaluates.lookup finalN) (.cons (Evaluates.lookup finalD) .nil)) rfl
    rfl
  · rfl

theorem naive.«Returns» : (HeapCalls.scalarFunction program "naive" []).Returns := by
  obtain ⟨_, returned⟩ := naive.result []
  exact returned.scalar_returns

theorem naive.«Supported» : (HeapCalls.scalarFunction program "naive" []).Supported := naive.«Returns».supported

end data.«project-euler-statements».data.py.project_euler_statements.p33
