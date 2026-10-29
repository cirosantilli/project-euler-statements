import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p51.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.ComprehensionCalls
import lang.py.FormalSW.MembershipCalls
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerSolutions.Lib.FilteredSum
import ProjectEulerStatements.P51

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p51
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions.HeapCollection
private abbrev program := P51Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private def numbers (items : List Int) : List Mutable.Value := items.map number

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 6 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["replace_at", "family_numbers", "prime_family_size", "has_prime_family", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

namespace replace_at
def replaceFrom (indices : List Int) (digit : Int) (position : Nat) : List Int → List Int
  | [] => []
  | head :: tail => (if (position : Int) ∈ indices then digit else head) :: replaceFrom indices digit (position + 1) tail

def values (items indices : List Int) (digit : Int) : List Int := replaceFrom indices digit 0 items

theorem replaceFrom_length (items indices : List Int) (digit : Int) (position : Nat) :
    (replaceFrom indices digit position items).length = items.length := by
  induction items generalizing position with
  | nil => rfl
  | cons head tail ih => simp [replaceFrom, ih]

@[simp] theorem values_length (items indices : List Int) (digit : Int) : (values items indices digit).length = items.length :=
  replaceFrom_length items indices digit 0

def positions (indices : List Int) : List Nat :=
  indices.filterMap (fun index => if 0 ≤ index then some index.toNat else none)

theorem mem_positions (indices : List Int) (position : Nat) :
    position ∈ positions indices ↔ (position : Int) ∈ indices := by
  simp only [positions, List.mem_filterMap]
  constructor
  · rintro ⟨index, member, selected⟩
    split_ifs at selected with nonnegative
    · have same : index = (position : Int) := by simp only [Option.some.injEq] at selected; omega
      simpa only [same] using member
  · intro member
    exact ⟨position, member, by simp⟩

@[simp] theorem positions_natural (indices : List Nat) : positions (indices.map Int.ofNat) = indices := by
  simp [positions, List.filterMap_map]

private theorem replaceFrom_natural (items : List Nat) (indices : List Int) (digit position : Nat) :
    replaceFrom indices digit position (items.map Int.ofNat) =
      (ProjectEulerStatements.P51.replaceAt.go (positions indices) digit items position).map Int.ofNat := by
  induction items generalizing position with
  | nil => rfl
  | cons head tail ih =>
      by_cases member : (position : Int) ∈ indices <;>
        simp [replaceFrom, ProjectEulerStatements.P51.replaceAt.go, mem_positions, member, ih]

/-- Ignoring negative positions and keeping duplicate positions gives the exact natural-digit statement. -/
theorem values_natural (items : List Nat) (indices : List Int) (digit : Nat) :
    values (items.map Int.ofNat) indices digit =
      (ProjectEulerStatements.P51.replaceAt items (positions indices) digit).map Int.ofNat :=
  replaceFrom_natural items indices digit 0

private def element : Expr := .ifExp (.membership (.name "i") (.name "idxs") false) (.name "d") (.name "x")
private def target : Expr := .tuple [.name "i", .name "x"]
private def generators : List (Expr × Expr × List Expr) :=
  [(target, .call (.name "enumerate") [.name "digits", .constant (.int 0)], [])]

private theorem element_result (heap : Mutable.Heap) (env : HeapCalls.Env) (address position : Nat) (indices : List Int)
    (digit value : Int) (getIndices : env "idxs" = some (.ref address)) (getPosition : env "i" = some (number position))
    (getDigit : env "d" = some (number digit)) (getValue : env "x" = some (number value))
    (found : heap[address]? = some (.list (numbers indices))) :
    Evaluates program env element heap (number (if (position : Int) ∈ indices then digit else value)) heap := by
  have tested : Evaluates program env (.membership (.name "i") (.name "idxs") false) heap
      (flag (decide ((position : Int) ∈ indices))) heap := by
    apply Evaluates.membership (needle := number position) (source := .ref address)
      (.cons (Evaluates.lookup getPosition) (.cons (Evaluates.lookup getIndices) .nil))
    exact membership_list_ints heap address position indices found false
  by_cases member : (position : Int) ∈ indices
  · simp only [member, if_true]
    exact Evaluates.conditional (flag := true) tested (by simp [member, Mutable.truth, scalarTruth]) (Evaluates.lookup getDigit)
  · simp only [member, if_false]
    exact Evaluates.conditional (flag := false) tested (by simp [member, Mutable.truth, scalarTruth]) (Evaluates.lookup getValue)

private theorem loop (items remaining indices : List Int) (digit : Int) (position : Nat) (suffix : items.drop position = remaining)
    (base : Mutable.Heap) (digitsAddress indicesAddress : Nat)
    (digitsFound : base[digitsAddress]? = some (.list (numbers items)))
    (indicesFound : base[indicesAddress]? = some (.list (numbers indices)))
    (collected : List Int) (env : HeapCalls.Env) (getIndices : env "idxs" = some (.ref indicesAddress))
    (getDigit : env "d" = some (number digit)) :
    ∃ finalEnv, BlockContinues program env
      [.enumerateStepLoop "i" "x" (.ref digitsAddress) position position [.comprehensionAppend base.length element] []]
      (working base (numbers collected) []) finalEnv (working base (numbers (collected ++ replaceFrom indices digit position remaining)) []) := by
  induction remaining generalizing position collected env with
  | nil =>
      refine ⟨env, ?_⟩
      simp only [replaceFrom, List.append_nil]
      apply BlockContinues.enumerate_done (items := numbers items)
        (by simp [sequenceValue, Mutable.sequence, working, prefix_found base _ _ _ digitsFound])
      · have missing : items[position]? = none := by simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
        simp [numbers, missing]
      · exact .nil
  | cons head tail ih =>
      let bound := setLocal (setLocal env "i" (number position)) "x" (number head)
      let value := if (position : Int) ∈ indices then digit else head
      have boundIndices : bound "idxs" = some (.ref indicesAddress) := by simpa [bound, setLocal] using getIndices
      have boundDigit : bound "d" = some (number digit) := by simpa [bound, setLocal] using getDigit
      have evaluated := element_result (working base (numbers collected) []) bound indicesAddress position indices digit head
        boundIndices (by simp [bound, setLocal]) boundDigit (by simp [bound, setLocal])
        (by simp [working, prefix_found base _ _ _ indicesFound])
      have emitted : BlockContinues program bound [.comprehensionAppend base.length element]
          (working base (numbers collected) []) bound (working base (numbers (collected ++ [value])) []) := by
        simpa only [numbers, List.map_append, List.map_cons, List.map_nil, List.append_nil] using
          emit base (numbers collected) [] [] (number value) (by simpa only [List.append_nil] using evaluated)
      obtain ⟨finalEnv, rest⟩ := ih (position + 1) (by simp [List.drop_add_one_eq_tail_drop, suffix])
        (collected ++ [value]) bound boundIndices boundDigit
      refine ⟨finalEnv, ?_⟩
      have selected : items[position]? = some head := by simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
      apply BlockContinues.enumerate_step (items := numbers items) (value := number head)
        (by simp [sequenceValue, Mutable.sequence, working, prefix_found base _ _ _ digitsFound]) (by simp [numbers, selected])
      simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_eq_true, if_false,
        replaceFrom, value, Int.natCast_add, Int.natCast_one, List.append_assoc, List.singleton_append] using emitted.append rest

/-- Signed values, duplicate or out-of-range indices, and aliased input lists all preserve their original objects. -/
theorem result (items indices : List Int) (digit : Int) (heap : Mutable.Heap) (digitsAddress indicesAddress : Nat)
    (digitsFound : heap[digitsAddress]? = some (.list (numbers items)))
    (indicesFound : heap[indicesAddress]? = some (.list (numbers indices))) :
    ReturnsValue program "replace_at" [.ref digitsAddress, .ref indicesAddress, number digit] heap (.ref heap.length)
      (heap ++ [.list (numbers (values items indices digit))]) := by
  let initial := functionEnv ((findFunctionIn program.body "replace_at").getD ([], [])).1
    ((findFunctionIn program.body "replace_at").getD ([], [])).2 [.ref digitsAddress, .ref indicesAddress, number digit] []
  let inner := comprehensionTargetsEnv initial generators
  obtain ⟨finalEnv, scanned⟩ := loop items items indices digit 0 rfl heap digitsAddress indicesAddress digitsFound indicesFound [] inner
    (by simp [inner, generators, target, comprehensionTargetsEnv, targetLocals]; rfl)
    (by simp [inner, generators, target, comprehensionTargetsEnv, targetLocals]; rfl)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.list_comp_targets_enumerate (source := .ref digitsAddress) (startValue := number 0) (middle := heap)
    (items := numbers items) (first := 0) (index := "i") (name := "x")
    (.cons (Evaluates.lookup rfl) (.cons Evaluates.constant .nil)) rfl (by simp [Mutable.sequence, digitsFound]) rfl
  simpa only [working, values, numbers, List.map_nil, List.nil_append] using scanned

theorem «Returns» (heap : Mutable.Heap) (digitsAddress indicesAddress : Nat) (digit : Int) (_valid : heap.Valid)
    (digitsTyped : Mutable.Value.HasType heap (.ref digitsAddress) "list[int]")
    (indicesTyped : Mutable.Value.HasType heap (.ref indicesAddress) "list[int]") :
    (HeapCalls.call program "replace_at" [.ref digitsAddress, .ref indicesAddress, number digit] heap).Returns := by
  obtain ⟨items, digitsFound⟩ := Mutable.Value.ints_of_hasType digitsTyped
  obtain ⟨indices, indicesFound⟩ := Mutable.Value.ints_of_hasType indicesTyped
  exact (result items indices digit heap digitsAddress indicesAddress digitsFound indicesFound).returns

theorem «Supported» (heap : Mutable.Heap) (digitsAddress indicesAddress : Nat) (digit : Int) (valid : heap.Valid)
    (digitsTyped : Mutable.Value.HasType heap (.ref digitsAddress) "list[int]")
    (indicesTyped : Mutable.Value.HasType heap (.ref indicesAddress) "list[int]") :
    (HeapCalls.call program "replace_at" [.ref digitsAddress, .ref indicesAddress, number digit] heap).Supported :=
  («Returns» heap digitsAddress indicesAddress digit valid digitsTyped indicesTyped).supported
end replace_at

namespace family_numbers
private def naturals (items : List Nat) : List Mutable.Value := items.map (fun (item : Nat) => number item)
private def replaced (items : List Nat) (indices : List Int) (digit : Nat) : List Nat :=
  ProjectEulerStatements.P51.replaceAt items (replace_at.positions indices) digit
private def value (items : List Nat) (indices : List Int) (digit : Nat) : Nat :=
  Nat.ofDigits 10 (replaced items indices digit)
private def selected (items : List Nat) (indices : List Int) (digit : Nat) : Option Nat :=
  if (Nat.digits 10 (value items indices digit)).length = items.length then some (value items indices digit) else none
private def temporaries (items : List Nat) (indices : List Int) (digit : Nat) : Mutable.Heap :=
  [.list (naturals (replaced items indices digit)), .list (naturals (Nat.digits 10 (value items indices digit)))]
private def converted : Expr := .call (.name "of_digits_le") [.call (.name "replace_at") [.name "digits", .name "idxs", .name "d"]]
private def condition : Expr := .compare (.builtinCall .len [.call (.name "digits_le") [.name "m"]]) [(.eq, .name "length")]
private def accepted : List Stmt := [.expr (.call (.attribute (.name "out") "append") [.name "m"])]
private def body : List Stmt := [.assign [.name "m"] converted, .ifThen condition accepted []]

private structure Locals (env : HeapCalls.Env) (digitsAddress indicesAddress collector size : Nat) : Prop where
  getDigits : env "digits" = some (.ref digitsAddress)
  getIndices : env "idxs" = some (.ref indicesAddress)
  getOut : env "out" = some (.ref collector)
  getLength : env "length" = some (number size)

private theorem Locals.set (locals : Locals env digitsAddress indicesAddress collector size) (name : String) (item : Mutable.Value)
    (unused : name ∉ ["digits", "idxs", "out", "length"]) :
    Locals (setLocal env name item) digitsAddress indicesAddress collector size := by
  have stable (query : String) (member : query ∈ ["digits", "idxs", "out", "length"]) :
      setLocal env name item query = env query := by
    have different : query ≠ name := by intro same; subst query; exact unused member
    simp [setLocal, different]
  exact ⟨(stable "digits" (by simp)).trans locals.getDigits, (stable "idxs" (by simp)).trans locals.getIndices,
    (stable "out" (by simp)).trans locals.getOut, (stable "length" (by simp)).trans locals.getLength⟩

private theorem converted_result (items : List Nat) (indices : List Int) (digit : Nat)
    (heap : Mutable.Heap) (digitsAddress indicesAddress : Nat) (env : HeapCalls.Env)
    (digitsFound : heap[digitsAddress]? = some (.list (naturals items)))
    (indicesFound : heap[indicesAddress]? = some (.list (numbers indices)))
    (getDigits : env "digits" = some (.ref digitsAddress)) (getIndices : env "idxs" = some (.ref indicesAddress))
    (getDigit : env "d" = some (number digit)) :
    Evaluates program env converted heap (number (value items indices digit))
      (heap ++ [.list (naturals (replaced items indices digit))]) := by
  have replacement := replace_at.result (items.map Int.ofNat) indices digit heap digitsAddress indicesAddress
    (by simpa only [naturals, numbers, List.map_map, Function.comp_def] using digitsFound) indicesFound
  rw [replace_at.values_natural] at replacement
  have replacement' : Evaluates program env (.call (.name "replace_at") [.name "digits", .name "idxs", .name "d"])
      heap (.ref heap.length) (heap ++ [.list (naturals (replaced items indices digit))]) := by
    apply Evaluates.call (.cons (Evaluates.lookup getDigits) (.cons (Evaluates.lookup getIndices) (.cons (Evaluates.lookup getDigit) .nil)))
    simpa only [naturals, numbers, replaced, List.map_map, Function.comp_def] using replacement
  have conversion := common.of_digits_le.result ((replaced items indices digit).map Int.ofNat) 10
    (heap ++ [.list (naturals (replaced items indices digit))]) heap.length
    (by simp [naturals, List.map_map, Function.comp_def])
  have naturalValue : ProjectEulerStatements.PositionalDigits.value 10 ((replaced items indices digit).map Int.ofNat) =
      ((Nat.ofDigits 10 (replaced items indices digit) : Nat) : Int) := by
    simpa only [Nat.cast_ofNat] using ProjectEulerStatements.PositionalDigits.value_naturals 10 (replaced items indices digit)
  rw [naturalValue] at conversion
  have defaulted := ReturnsValue.with_defaults (supplied := [.ref heap.length]) rfl rfl rfl conversion
  apply Evaluates.call (.cons replacement' .nil)
  exact defaulted.extend common_extension

private theorem condition_result (items : List Nat) (indices : List Int) (digit : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getValue : env "m" = some (number (value items indices digit))) (getLength : env "length" = some (number items.length)) :
    Evaluates program env condition heap
      (flag (decide ((Nat.digits 10 (value items indices digit)).length = items.length)))
      (heap ++ [.list (naturals (Nat.digits 10 (value items indices digit)))]) := by
  have digits : Evaluates program env (.call (.name "digits_le") [.name "m"]) heap (.ref heap.length)
      (heap ++ [.list (naturals (Nat.digits 10 (value items indices digit)))]) := by
    apply Evaluates.call (.cons (Evaluates.lookup getValue) .nil)
    exact (common.digits_le.decimal (value items indices digit) heap).extend common_extension
  have length : Evaluates program env (.builtinCall .len [.call (.name "digits_le") [.name "m"]]) heap
      (number (Nat.digits 10 (value items indices digit)).length)
      (heap ++ [.list (naturals (Nat.digits 10 (value items indices digit)))]) :=
    Evaluates.builtin (.cons digits .nil) (by simp [primitive, Mutable.length, naturals])
  exact Evaluates.compare length (Evaluates.lookup getLength) (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])

private theorem cell_result (items : List Nat) (indices : List Int) (digit : Nat)
    (base garbage : Mutable.Heap) (before : List Nat) (digitsAddress indicesAddress : Nat)
    (digitsFound : base[digitsAddress]? = some (.list (naturals items)))
    (indicesFound : base[indicesAddress]? = some (.list (numbers indices))) (env : HeapCalls.Env)
    (locals : Locals env digitsAddress indicesAddress base.length items.length)
    (getDigit : env "d" = some (number digit)) :
    BlockContinues program env body (working base (naturals before) garbage)
      (setLocal env "m" (number (value items indices digit)))
      (working base (naturals (before ++ (selected items indices digit).toList)) (garbage ++ temporaries items indices digit)) := by
  let heap := working base (naturals before) garbage
  let middle := heap ++ [.list (naturals (replaced items indices digit))]
  let ready := setLocal env "m" (number (value items indices digit))
  have assigned : BlockContinues program env [.assign [.name "m"] converted] heap ready middle := by
    apply BlockContinues.assign
    exact converted_result items indices digit heap digitsAddress indicesAddress env
      (by simp [heap, working, prefix_found base _ _ _ digitsFound])
      (by simp [heap, working, prefix_found base _ _ _ indicesFound]) locals.getDigits locals.getIndices getDigit
  have tested := condition_result items indices digit middle ready (by simp [ready, setLocal])
    (by simpa [ready, setLocal] using locals.getLength)
  have readyLocals := locals.set "m" (number (value items indices digit)) (by simp)
  apply assigned.append
  by_cases sameWidth : (Nat.digits 10 (value items indices digit)).length = items.length
  · apply BlockContinues.branch (flag := true) tested (by simp [sameWidth, Mutable.truth, scalarTruth])
    apply BlockContinues.discard
    have receiver := Evaluates.lookup (globals := []) (module := program) (heap := middle ++ [.list (naturals (Nat.digits 10 (value items indices digit)))]) readyLocals.getOut
    have found : (middle ++ [.list (naturals (Nat.digits 10 (value items indices digit)))])[base.length]? = some (.list (naturals before)) := by
      simp only [middle, heap, ProjectEulerSolutions.HeapCollection.append]
      exact ProjectEulerSolutions.HeapCollection.found base _ _
    have appended := Evaluates.append receiver found (Evaluates.lookup (name := "m") (value := number (value items indices digit)) (by simp [setLocal])) found
    simpa only [selected, sameWidth, if_true, Option.toList_some, temporaries, naturals, List.map_append,
      List.map_cons, List.map_nil, middle, heap, List.append_assoc, List.singleton_append,
      ProjectEulerSolutions.HeapCollection.append, store] using appended
  · apply BlockContinues.branch (flag := false) tested (by simp [sameWidth, Mutable.truth, scalarTruth])
    have unchanged : middle ++ [.list (naturals (Nat.digits 10 (value items indices digit)))] =
        working base (naturals before) (garbage ++ temporaries items indices digit) := by
      dsimp [middle, heap, working, temporaries]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    simp only [Bool.false_eq_true, if_false, selected, sameWidth, Option.toList_none, List.append_nil]
    rw [← unchanged]
    exact .nil

private theorem loop (items : List Nat) (indices : List Int) (first count : Nat) (bound : first + count = 10)
    (base garbage : Mutable.Heap) (before : List Nat) (digitsAddress indicesAddress : Nat)
    (digitsFound : base[digitsAddress]? = some (.list (naturals items)))
    (indicesFound : base[indicesAddress]? = some (.list (numbers indices))) (env : HeapCalls.Env)
    (locals : Locals env digitsAddress indicesAddress base.length items.length) :
    ∃ finalEnv finalGarbage,
      BlockContinues program env [.rangeStepLoop "d" first 10 1 body []] (working base (naturals before) garbage) finalEnv
        (working base (naturals (before ++ (List.range' first count).filterMap (selected items indices))) finalGarbage) ∧
      Locals finalEnv digitsAddress indicesAddress base.length items.length := by
  induction count generalizing first garbage before env with
  | zero =>
      refine ⟨env, garbage, ?_, locals⟩
      simp only [List.range'_zero, List.filterMap_nil, List.append_nil]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
  | succ count ih =>
      let boundEnv := setLocal env "d" (number first)
      have boundLocals := locals.set "d" (number first) (by simp)
      have stepped := cell_result items indices first base garbage before digitsAddress indicesAddress digitsFound indicesFound
        boundEnv boundLocals (by simp [boundEnv, setLocal])
      let ready := setLocal boundEnv "m" (number (value items indices first))
      have readyLocals := boundLocals.set "m" (number (value items indices first)) (by simp)
      obtain ⟨finalEnv, finalGarbage, rest, finalLocals⟩ := ih (first + 1) (by omega)
        (garbage ++ temporaries items indices first) (before ++ (selected items indices first).toList) ready readyLocals
      refine ⟨finalEnv, finalGarbage, ?_, finalLocals⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      cases selection : selected items indices first <;>
        simpa only [Calls.loopContinuation, show Calls.loopControl body = false from rfl, Bool.false_eq_true, if_false,
          Int.natCast_add, Int.natCast_one, List.range'_succ, List.filterMap_cons, List.append_assoc,
          selection, Option.toList_none, Option.toList_some, List.nil_append, List.singleton_append] using stepped.append rest

/-- The source retains exactly those replacements with the original decimal width, preserving the input heap prefix. -/
theorem result (n : Nat) (indices : List Int) (heap : Mutable.Heap) (indicesAddress : Nat)
    (indicesFound : heap[indicesAddress]? = some (.list (numbers indices))) :
    ∃ garbage, ReturnsValue program "family_numbers" [number n, .ref indicesAddress] heap (.ref (heap.length + 1))
      (working (heap ++ [.list (naturals (Nat.digits 10 n))])
        (naturals (ProjectEulerStatements.P51.familyNumbers n (replace_at.positions indices))) garbage) := by
  let items := Nat.digits 10 n
  let base := heap ++ [.list (naturals items)]
  let initial := functionEnv ((findFunctionIn program.body "family_numbers").getD ([], [])).1
    ((findFunctionIn program.body "family_numbers").getD ([], [])).2 [number n, .ref indicesAddress] []
  let withDigits := setLocal initial "digits" (.ref heap.length)
  let withLength := setLocal withDigits "length" (number items.length)
  let ready := setLocal withLength "out" (.ref base.length)
  have digitsFound : base[heap.length]? = some (.list (naturals items)) := by simp [base]
  have locals : Locals ready heap.length indicesAddress base.length items.length := by
    constructor <;> simp [ready, withLength, withDigits, setLocal]
    rfl
  obtain ⟨finalEnv, garbage, scanned, finalLocals⟩ := loop items indices 0 10 rfl base [] [] heap.length indicesAddress
    digitsFound (prefix_found heap _ _ _ indicesFound) ready locals
  have enumeration : (List.range' 0 10).filterMap (selected items indices) =
      ProjectEulerStatements.P51.familyNumbers n (replace_at.positions indices) := by
    rw [← List.range_eq_range']
    rfl
  refine ⟨garbage, ?_⟩
  change ReturnsValue program "family_numbers" [number n, .ref indicesAddress] heap (.ref (heap.length + 1))
    (working base (naturals (ProjectEulerStatements.P51.familyNumbers n (replace_at.positions indices))) garbage)
  have baseLength : base.length = heap.length + 1 := by simp [base]
  rw [← baseLength]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := .ref heap.length) (middle := base)
  · apply Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
    exact (common.digits_le.decimal n heap).extend common_extension
  apply BlockReturns.assign (value := number items.length) (middle := base)
  · apply Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil)
    simp [primitive, Mutable.length, digitsFound, naturals]
  apply BlockReturns.assign (value := .ref base.length) (middle := working base (naturals []) [])
  · exact Evaluates.list .nil
  have enumerated : BlockContinues program ready [.forIn (.name "d") (.call (.name "range") [.constant (.int 10)]) body []]
      (working base (naturals []) []) finalEnv
      (working base (naturals (ProjectEulerStatements.P51.familyNumbers n (replace_at.positions indices))) garbage) := by
    apply BlockContinues.for_range (.cons Evaluates.constant .nil) rfl
    simpa only [enumeration, List.nil_append] using scanned
  exact enumerated.returns (BlockReturns.return_value (Evaluates.lookup finalLocals.getOut))

end family_numbers


private def familyEnv (n : Int) : HeapCalls.Env := fun name => if name = "n" then some (number n) else none
private theorem family_condition (n : Int) (heap : Mutable.Heap) :
    Evaluates program (familyEnv n) P51Ast.requires_family_numbers_0 heap (flag (decide (0 ≤ n))) heap := by
  apply Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
  simp [HeapCalls.compare, scalarCompare, evalCmpOp]

theorem family_numbers.«Returns» (heap : Mutable.Heap) (n : Int) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (condition : HeapCalls.Condition program (familyEnv n) P51Ast.requires_family_numbers_0 heap) :
    (HeapCalls.call program "family_numbers" [number n, .ref address] heap).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [Mutable.truth, scalarTruth] using (family_condition n heap).condition_iff.mp condition
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  obtain ⟨garbage, returned⟩ := family_numbers.result n.toNat items heap address found
  simpa only [Int.toNat_of_nonneg nonnegative] using returned.returns

theorem family_numbers.«Supported» (heap : Mutable.Heap) (n : Int) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (condition : HeapCalls.Condition program (familyEnv n) P51Ast.requires_family_numbers_0 heap) :
    (HeapCalls.call program "family_numbers" [number n, .ref address] heap).Supported :=
  (family_numbers.«Returns» heap n address valid typed condition).supported

theorem requires_family_numbers_0_supported (heap : Mutable.Heap) (n : Int) (_address : Nat) (_valid : heap.Valid)
    (_typed : Mutable.Value.HasType heap (.ref _address) "list[int]") :
    (HeapCalls.evaluate program (familyEnv n) P51Ast.requires_family_numbers_0 heap).Supported :=
  Execution.supported_of_finishes (family_condition n heap).finishes


namespace prime_family_size
private def naturals (items : List Nat) : List Mutable.Value := items.map (fun (item : Nat) => number item)
private abbrev predicate : Expr := .call (.name "is_prime") [.name "m"]
private abbrev iterable : Expr := .call (.name "family_numbers") [.name "n", .name "idxs"]
private abbrev expression : Expr := .sumGenerator (.constant (.int 1)) [("m", iterable, [predicate])] (.constant (.int 0))

private theorem count_fold (items : List Nat) (initial : Int) :
    items.foldl (fun total item => if ProjectEulerStatements.P51.isPrime item then total + 1 else total) initial =
      initial + ((items.filter ProjectEulerStatements.P51.isPrime).length : Nat) := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
      cases prime : ProjectEulerStatements.P51.isPrime head <;>
        simp [List.foldl_cons, prime, ih, Int.add_comm, Int.add_left_comm]

/-- Count the original lazy generator's prime tests without allocating any extra collector. -/
theorem result (n : Nat) (indices : List Int) (heap : Mutable.Heap) (address : Nat)
    (indicesFound : heap[address]? = some (.list (numbers indices))) :
    ∃ extra, ReturnsValue program "prime_family_size" [number n, .ref address] heap
      (number (ProjectEulerStatements.P51.primeFamilySize n (replace_at.positions indices))) (heap ++ extra) := by
  obtain ⟨garbage, family⟩ := family_numbers.result n indices heap address indicesFound
  let values := ProjectEulerStatements.P51.familyNumbers n (replace_at.positions indices)
  let middle := working (heap ++ [.list (naturals (Nat.digits 10 n))]) (naturals values) garbage
  let env := functionEnv ((findFunctionIn program.body "prime_family_size").getD ([], [])).1
    ((findFunctionIn program.body "prime_family_size").getD ([], [])).2 [number n, .ref address] []
  have found : middle[heap.length + 1]? = some (.list (naturals values)) := by simp [middle, working]
  have family' : ReturnsValue program "family_numbers" [number n, .ref address] heap (.ref (heap.length + 1)) middle := family
  let inner := setLocal (comprehensionEnv env [("m", iterable, [predicate])]) sumAccumulator (number 0)
  have evaluated : Evaluates program env expression heap
      (number (ProjectEulerStatements.P51.primeFamilySize n (replace_at.positions indices))) middle := by
    apply Evaluates.sum_generator_sequence (items := naturals values) (by intros; simp)
      (Evaluates.call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) family')
      (by simp [Mutable.sequence, found]) Evaluates.constant rfl
    have summed := ProjectEulerSolutions.FilteredSum.loop (program := program) (values := values)
      (encode := fun (item : Nat) => number item) (predicate := ProjectEulerStatements.P51.isPrime)
      (number := fun _ => 1) (heap := middle) (name := "m") (source := .ref (heap.length + 1)) (position := 0) (env := inner)
      (element := .constant (.int 1)) (test := predicate) (initial := 0) values (by decide)
      (by simp [sequenceValue, Mutable.sequence, found]; rfl)
      (fun env item getItem => Evaluates.call (.cons (Evaluates.lookup getItem) .nil)
        ((common.is_prime.heap_result item middle).extend common_extension))
      (fun _ _ _ _ => Evaluates.constant) rfl (by simp [inner, setLocal])
    simpa only [count_fold, Int.zero_add, ProjectEulerStatements.P51.primeFamilySize, values] using summed
  refine ⟨[.list (naturals (Nat.digits 10 n)), .list (naturals values)] ++ garbage, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  simpa only [middle, working, List.append_assoc, List.cons_append, List.nil_append] using evaluated
end prime_family_size

private theorem size_condition (n : Int) (heap : Mutable.Heap) :
    Evaluates program (familyEnv n) P51Ast.requires_prime_family_size_0 heap (flag (decide (0 ≤ n))) heap := by
  apply Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
  simp [HeapCalls.compare, scalarCompare, evalCmpOp]

theorem prime_family_size.«Returns» (heap : Mutable.Heap) (n : Int) (address : Nat) (_valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (condition : HeapCalls.Condition program (familyEnv n) P51Ast.requires_prime_family_size_0 heap) :
    (HeapCalls.call program "prime_family_size" [number n, .ref address] heap).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [Mutable.truth, scalarTruth] using (size_condition n heap).condition_iff.mp condition
  obtain ⟨items, found⟩ := Mutable.Value.ints_of_hasType typed
  obtain ⟨garbage, returned⟩ := prime_family_size.result n.toNat items heap address found
  simpa only [Int.toNat_of_nonneg nonnegative] using returned.returns

theorem prime_family_size.«Supported» (heap : Mutable.Heap) (n : Int) (address : Nat) (valid : heap.Valid)
    (typed : Mutable.Value.HasType heap (.ref address) "list[int]")
    (condition : HeapCalls.Condition program (familyEnv n) P51Ast.requires_prime_family_size_0 heap) :
    (HeapCalls.call program "prime_family_size" [number n, .ref address] heap).Supported :=
  (prime_family_size.«Returns» heap n address valid typed condition).supported

theorem requires_prime_family_size_0_supported (heap : Mutable.Heap) (n : Int) (address : Nat) (_valid : heap.Valid)
    (_typed : Mutable.Value.HasType heap (.ref address) "list[int]") :
    (HeapCalls.evaluate program (familyEnv n) P51Ast.requires_prime_family_size_0 heap).Supported :=
  Execution.supported_of_finishes (size_condition n heap).finishes


namespace sublists
/-- The source prefixes each newly read element, reversing every ordinary sublist. -/
def values (items : List Int) : List (List Int) := items.sublists.map List.reverse

theorem values_concat (items : List Int) (item : Int) :
    values (items ++ [item]) = values items ++ (values items).map (item :: ·) := by
  simp [values, List.sublists_concat, List.map_map, Function.comp_def]

private def refs (addresses : List Nat) : List Mutable.Value := addresses.map Mutable.Value.ref
private def Rows (heap : Mutable.Heap) (forbidden addresses : List Nat) (rows : List (List Int)) : Prop :=
  List.Forall₂ (fun address row => address ∉ forbidden ∧ heap[address]? = some (.list (numbers row))) addresses rows

private theorem Rows.extend {values : List (List Int)} (rows : Rows heap forbidden addresses values) (extra : Mutable.Heap) :
    Rows (heap ++ extra) forbidden addresses values := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.1, prefix_found heap extra _ _ head.2⟩ ih

private theorem Rows.store {values : List (List Int)} (rows : Rows heap forbidden addresses values) (address : Nat) (member : address ∈ forbidden)
    (replacement : Mutable.Object) : Rows (heap.set address replacement) forbidden addresses values := by
  induction rows with
  | nil => exact .nil
  | cons head tail ih =>
      refine .cons ⟨head.1, ?_⟩ ih
      rw [List.getElem?_set_ne (by intro same; subst address; exact head.1 member)]
      exact head.2

private theorem Rows.change {values : List (List Int)} (rows : Rows (working base old garbage) [outAddress, base.length] addresses values)
    (replacement : List Mutable.Value) (extra : Mutable.Heap) :
    Rows (working base replacement (garbage ++ extra)) [outAddress, base.length] addresses values := by
  have changed := (rows.extend extra).store base.length (by simp) (.list replacement)
  simpa only [ProjectEulerSolutions.HeapCollection.append, ProjectEulerSolutions.HeapCollection.store] using changed

private def element : Expr := .binOp (.list [.name "x"]) .add (.name "ys")
private def generators : List (String × Expr × List Expr) := [("ys", .name "out", [])]

private theorem element_result (heap : Mutable.Heap) (env : HeapCalls.Env) (item : Int) (address : Nat) (row : List Int)
    (getItem : env "x" = some (number item)) (getRow : env "ys" = some (.ref address))
    (rowFound : heap[address]? = some (.list (numbers row))) :
    Evaluates program env element heap (.ref (heap.length + 1))
      (heap ++ [.list [number item], .list (numbers (item :: row))]) := by
  apply Evaluates.binary (av := .ref heap.length) (bv := .ref address)
    (middle := heap ++ [.list [number item]]) (afterRight := heap ++ [.list [number item]])
  · exact Evaluates.list (.cons (Evaluates.lookup getItem) .nil)
  · exact Evaluates.lookup getRow
  · have input := prefix_found heap [.list [number item]] _ _ rowFound
    simp [Mutable.binary, show (BinOp.add == BinOp.add) = true from rfl, Mutable.array, Mutable.allocate, input, numbers, List.append_assoc, Except.map]

private theorem comprehension_loop (inputAddresses : List Nat) (outAddress : Nat) (item : Int)
    (base : Mutable.Heap) (sourceFound : base[outAddress]? = some (.list (refs inputAddresses)))
    (remainingAddresses : List Nat) (remainingRows : List (List Int))
    (remaining : List.Forall₂ (fun address row => base[address]? = some (.list (numbers row))) remainingAddresses remainingRows)
    (position : Nat) (suffix : inputAddresses.drop position = remainingAddresses)
    (collected : List Nat) (before : List (List Int)) (garbage : Mutable.Heap)
    (rows : Rows (working base (refs collected) garbage) [outAddress, base.length] collected before)
    (env : HeapCalls.Env) (getItem : env "x" = some (number item)) :
    ∃ finalEnv addresses finalGarbage,
      BlockContinues program env
        [.sequenceStepLoop "ys" (.ref outAddress) position [.comprehensionAppend base.length element] []]
        (working base (refs collected) garbage) finalEnv (working base (refs addresses) finalGarbage) ∧
      Rows (working base (refs addresses) finalGarbage) [outAddress, base.length] addresses
        (before ++ remainingRows.map (item :: ·)) := by
  induction remaining generalizing position collected before garbage env with
  | nil =>
      refine ⟨env, collected, garbage, ?_, ?_⟩
      · apply BlockContinues.sequence_done (items := refs inputAddresses)
          (by simp [sequenceValue, Mutable.sequence, working, prefix_found base _ _ _ sourceFound])
        · have missing : inputAddresses[position]? = none := by
            simpa [suffix] using (List.head?_drop (l := inputAddresses) (i := position)).symm
          simp [refs, missing]
        · exact .nil
      · simpa only [List.map_nil, List.append_nil] using rows
  | @cons address row tailAddresses tailRows headFound tailFound ih =>
      let heap := working base (refs collected) garbage
      let bound := setLocal env "ys" (.ref address)
      let extra : Mutable.Heap := [.list [number item], .list (numbers (item :: row))]
      let fresh := heap.length + 1
      let nextAddresses := collected ++ [fresh]
      have boundItem : bound "x" = some (number item) := by simpa [bound, setLocal] using getItem
      have evaluated := element_result heap bound item address row boundItem (by simp [bound, setLocal])
        (by simp [heap, working, prefix_found base _ _ _ headFound])
      have emitted : BlockContinues program bound [.comprehensionAppend base.length element] heap bound
          (working base (refs nextAddresses) (garbage ++ extra)) := by
        simpa only [heap, fresh, nextAddresses, refs, List.map_append, List.map_cons, List.map_nil] using
          emit base (refs collected) garbage extra (.ref fresh) evaluated
      have freshFound : (working base (refs nextAddresses) (garbage ++ extra))[fresh]? = some (.list (numbers (item :: row))) := by
        have allocated : (heap ++ extra)[fresh]? = some (.list (numbers (item :: row))) := by simp [extra, fresh]
        have preserved := List.getElem?_set_ne (l := heap ++ extra) (a := Mutable.Object.list (refs nextAddresses))
          (show base.length ≠ fresh by simp [fresh, heap, working]; omega)
        simpa only [heap, ProjectEulerSolutions.HeapCollection.append, store] using preserved.trans allocated
      have newRows : Rows (working base (refs nextAddresses) (garbage ++ extra)) [outAddress, base.length]
          nextAddresses (before ++ [item :: row]) := by
        apply List.rel_append (rows.change (refs nextAddresses) extra)
        exact .cons ⟨by
          have within := (List.getElem?_eq_some_iff.mp sourceFound).1
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          constructor <;> (intro same; simp [fresh, heap, working] at same; omega), freshFound⟩ .nil
      obtain ⟨finalEnv, addresses, finalGarbage, rest, finalRows⟩ := ih (position + 1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) nextAddresses (before ++ [item :: row])
        (garbage ++ extra) newRows bound boundItem
      refine ⟨finalEnv, addresses, finalGarbage, ?_, ?_⟩
      · have selected : inputAddresses[position]? = some address := by
          simpa [suffix] using (List.head?_drop (l := inputAddresses) (i := position)).symm
        apply BlockContinues.sequence_step (items := refs inputAddresses) (value := .ref address)
          (by simp [sequenceValue, Mutable.sequence, working, prefix_found base _ _ _ sourceFound]) (by simp [refs, selected])
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_eq_true,
          if_false] using emitted.append rest
      · simpa only [List.map_cons, List.append_assoc, List.singleton_append] using finalRows

private theorem Rows.forget_collector (rows : Rows heap [outAddress, collector] addresses rowsValues) :
    Rows heap [outAddress] addresses rowsValues := by
  apply List.Forall₂.imp ?_ rows
  intro address row represented
  exact ⟨fun member => represented.1 (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp member))), represented.2⟩

private def expression : Expr := .listComp element generators
private def body : List Stmt := [.augAssign (.name "out") .add expression]

private theorem comprehension (item : Int) (heap : Mutable.Heap) (outAddress : Nat)
    (addresses : List Nat) (rowValues : List (List Int))
    (found : heap[outAddress]? = some (.list (refs addresses)))
    (represented : Rows heap [outAddress] addresses rowValues) (env : HeapCalls.Env)
    (getItem : env "x" = some (number item)) (getOut : env "out" = some (.ref outAddress)) :
    ∃ newAddresses garbage,
      Evaluates program env expression heap (.ref heap.length) (working heap (refs newAddresses) garbage) ∧
      Rows (working heap (refs newAddresses) garbage) [outAddress, heap.length] newAddresses (rowValues.map (item :: ·)) := by
  have entries : List.Forall₂ (fun address row => heap[address]? = some (.list (numbers row))) addresses rowValues :=
    List.Forall₂.imp (fun _ _ represented => represented.2) represented
  obtain ⟨finalEnv, newAddresses, garbage, scanned, finalRows⟩ := comprehension_loop addresses outAddress item heap found
    addresses rowValues entries 0 rfl [] [] [] .nil (comprehensionEnv env generators)
    (by simpa [generators, comprehensionEnv] using getItem)
  refine ⟨newAddresses, garbage, ?_, ?_⟩
  · apply Evaluates.list_comp_sequence (items := refs addresses) (by intros; simp) (Evaluates.lookup getOut)
      (by simp [Mutable.sequence, found])
    simpa only [working, refs, List.map_nil] using scanned
  · simpa only [List.nil_append] using finalRows

private theorem loop (items remaining : List Int) (position : Nat) (suffix : items.drop position = remaining)
    (processed : List Int) (base garbage : Mutable.Heap) (inputAddress : Nat)
    (inputFound : base[inputAddress]? = some (.list (numbers items)))
    (addresses : List Nat) (rows : Rows (working base (refs addresses) garbage) [base.length] addresses (values processed))
    (env : HeapCalls.Env) (getOut : env "out" = some (.ref base.length)) :
    ∃ finalEnv finalAddresses finalGarbage,
      BlockContinues program env [.sequenceStepLoop "x" (.ref inputAddress) position body []]
        (working base (refs addresses) garbage) finalEnv (working base (refs finalAddresses) finalGarbage) ∧
      Rows (working base (refs finalAddresses) finalGarbage) [base.length] finalAddresses (values (processed ++ remaining)) ∧
      finalEnv "out" = some (.ref base.length) := by
  induction remaining generalizing position processed garbage addresses env with
  | nil =>
      refine ⟨env, addresses, garbage, ?_, ?_, getOut⟩
      · apply BlockContinues.sequence_done (items := numbers items)
          (by simp [sequenceValue, Mutable.sequence, working, prefix_found base _ _ _ inputFound])
        · have missing : items[position]? = none := by
            simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
          simp [numbers, missing]
        · exact .nil
      · simpa only [List.append_nil] using rows
  | cons head tail ih =>
      let heap := working base (refs addresses) garbage
      let bound := setLocal env "x" (number head)
      obtain ⟨newAddresses, allocated, evaluated, newRows⟩ := comprehension head heap base.length addresses (values processed)
        (by simp [heap]) rows bound (by simp [bound, setLocal]) (by simpa [bound, setLocal] using getOut)
      let newGarbage := garbage ++ (.list (refs newAddresses) :: allocated)
      let combined := addresses ++ newAddresses
      let ready := setLocal bound "out" (.ref base.length)
      have shape : working heap (refs newAddresses) allocated = working base (refs addresses) newGarbage := by
        dsimp [heap, newGarbage, working]
        simp only [List.append_assoc, List.cons_append]
      have outFound : (working heap (refs newAddresses) allocated)[base.length]? = some (.list (refs addresses)) := by
        rw [shape]
        simp
      have collectorFound : (working heap (refs newAddresses) allocated)[heap.length]? = some (.list (refs newAddresses)) := by simp
      have stored : (working heap (refs newAddresses) allocated).set base.length (.list (refs combined)) =
          working base (refs combined) newGarbage := by rw [shape, store]
      have stepped : BlockContinues program bound body heap ready (working base (refs combined) newGarbage) := by
        have operation := inplace_add_lists (working heap (refs newAddresses) allocated) base.length heap.length
          (refs addresses) (refs newAddresses) outFound collectorFound
        simp only [refs, ← List.map_append] at operation
        have assigned : BlockContinues program bound body heap ready
            ((working heap (refs newAddresses) allocated).set base.length (.list (refs combined))) :=
          BlockContinues.augAssign (name := "out") (by simpa [bound, setLocal] using getOut) evaluated operation
        simpa only [stored] using assigned
      have originalRows : Rows (working heap (refs newAddresses) allocated) [base.length] addresses (values processed) :=
        rows.extend (.list (refs newAddresses) :: allocated)
      have combinedRows : Rows (working base (refs combined) newGarbage) [base.length] combined (values (processed ++ [head])) := by
        rw [values_concat]
        have oldStored := originalRows.store base.length (by simp) (.list (refs combined))
        have newStored := newRows.forget_collector.store base.length (by simp) (.list (refs combined))
        rw [stored] at oldStored newStored
        exact List.rel_append oldStored newStored
      obtain ⟨finalEnv, finalAddresses, finalGarbage, rest, finalRows, finalOut⟩ := ih (position + 1)
        (by simp [List.drop_add_one_eq_tail_drop, suffix]) (processed ++ [head]) newGarbage combined combinedRows ready (by simp [ready, setLocal])
      refine ⟨finalEnv, finalAddresses, finalGarbage, ?_, ?_, finalOut⟩
      · have selected : items[position]? = some head := by
          simpa [suffix] using (List.head?_drop (l := items) (i := position)).symm
        apply BlockContinues.sequence_step (items := numbers items) (value := number head)
          (by simp [sequenceValue, Mutable.sequence, working, prefix_found base _ _ _ inputFound]) (by simp [numbers, selected])
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_eq_true, if_false] using stepped.append rest
      · simpa only [List.append_assoc, List.singleton_append] using finalRows

/-- Every returned row is a fresh list; existing lists and their aliases remain unchanged. -/
theorem result (items : List Int) (heap : Mutable.Heap) (address : Nat)
    (inputFound : heap[address]? = some (.list (numbers items))) :
    ∃ extra outAddress addresses, ReturnsValue program "sublists" [.ref address] heap (.ref outAddress) (heap ++ extra) ∧
      (heap ++ extra)[outAddress]? = some (.list (refs addresses)) ∧
      Rows (heap ++ extra) [outAddress] addresses (values items) := by
  let base := heap ++ [.list []]
  let initial := functionEnv ((findFunctionIn program.body "sublists").getD ([], [])).1
    ((findFunctionIn program.body "sublists").getD ([], [])).2 [.ref address] []
  let ready := setLocal initial "out" (.ref base.length)
  have represented : Rows (working base (refs [heap.length]) []) [base.length] [heap.length] (values []) := by
    apply List.Forall₂.cons ?_ .nil
    constructor
    · simp [base]
    · simp [base, working, numbers]
  obtain ⟨finalEnv, addresses, garbage, scanned, finalRows, finalOut⟩ := loop items items 0 rfl [] base [] address
    (prefix_found heap _ _ _ inputFound) [heap.length] represented ready (by simp [ready, setLocal])
  let extra := .list [] :: .list (refs addresses) :: garbage
  have finalShape : working base (refs addresses) garbage = heap ++ extra := by
    dsimp [working, base, extra]
    simp only [List.append_assoc, List.singleton_append]
  refine ⟨extra, base.length, addresses, ?_, ?_, ?_⟩
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.assign (value := .ref base.length) (middle := working base (refs [heap.length]) [])
    · apply Evaluates.list (.cons (Evaluates.list .nil) .nil)
    · have enumerated : BlockContinues program ready [.forIn (.name "x") (.name "xs") body []]
          (working base (refs [heap.length]) []) finalEnv (heap ++ extra) := by
        apply BlockContinues.for_sequence (items := numbers items) (by intros; simp) (Evaluates.lookup (by simp [ready, setLocal]; rfl))
          (by simp [Mutable.sequence, working, prefix_found base _ _ _ (prefix_found heap _ _ _ inputFound)])
        simpa only [finalShape] using scanned
      exact enumerated.returns (BlockReturns.return_value (Evaluates.lookup finalOut))
  · rw [← finalShape]
    simp
  · simpa only [finalShape, List.nil_append] using finalRows

end sublists


namespace has_prime_family
private def naturals (items : List Nat) : List Mutable.Value := items.map (fun (item : Nat) => number item)
private def familyValues (n : Nat) (indices : List Int) : List Nat :=
  ProjectEulerStatements.P51.familyNumbers n (replace_at.positions indices)
private def good (k : Int) (n : Nat) (indices : List Int) : Bool :=
  decide (n ∈ familyValues n indices) &&
    decide (k ≤ (ProjectEulerStatements.P51.primeFamilySize n (replace_at.positions indices) : Int))
private def element : Expr := .boolOp .and [
  .membership (.name "n") (.call (.name "family_numbers") [.name "n", .name "s"]) false,
  .compare (.call (.name "prime_family_size") [.name "n", .name "s"]) [(.gtE, .name "k")]]

private theorem membership_result (n : Nat) (indices : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers indices))) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) (getSubset : env "s" = some (.ref address)) :
    ∃ extra, Evaluates program env
      (.membership (.name "n") (.call (.name "family_numbers") [.name "n", .name "s"]) false)
      heap (flag (decide (n ∈ familyValues n indices))) (heap ++ extra) := by
  obtain ⟨garbage, family⟩ := family_numbers.result n indices heap address found
  let extra := .list (naturals (Nat.digits 10 n)) :: .list (naturals (familyValues n indices)) :: garbage
  have family' : ReturnsValue program "family_numbers" [number n, .ref address] heap (.ref (heap.length + 1)) (heap ++ extra) := by
    simpa only [extra, familyValues, naturals, family_numbers.naturals, working, List.append_assoc, List.cons_append, List.nil_append] using family
  refine ⟨extra, ?_⟩
  apply Evaluates.membership (needle := number n) (source := .ref (heap.length + 1))
    (.cons (Evaluates.lookup getN)
      (.cons (Evaluates.call (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getSubset) .nil)) family') .nil))
  have collection : (heap ++ extra)[heap.length + 1]? = some (.list (numbers ((familyValues n indices).map Int.ofNat))) := by
    simp [extra, naturals, numbers, List.map_map, Function.comp_def]
  simpa [List.mem_map, Int.natCast_inj] using
    membership_list_ints (heap ++ extra) (heap.length + 1) n ((familyValues n indices).map Int.ofNat) collection false

/-- The prime count runs only when the original number belongs to the generated family. -/
private theorem element_result (k : Int) (n : Nat) (indices : List Int) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers indices))) (env : HeapCalls.Env)
    (getK : env "k" = some (number k)) (getN : env "n" = some (number n)) (getSubset : env "s" = some (.ref address)) :
    ∃ extra, Evaluates program env element heap (flag (good k n indices)) (heap ++ extra) := by
  obtain ⟨allocated, tested⟩ := membership_result n indices heap address found env getN getSubset
  by_cases member : n ∈ familyValues n indices
  · obtain ⟨extra, counted⟩ := prime_family_size.result n indices (heap ++ allocated) address (prefix_found heap allocated _ _ found)
    have compared : Evaluates program env (.compare (.call (.name "prime_family_size") [.name "n", .name "s"]) [(.gtE, .name "k")])
        (heap ++ allocated) (flag (decide (k ≤ (ProjectEulerStatements.P51.primeFamilySize n (replace_at.positions indices) : Int))))
        ((heap ++ allocated) ++ extra) := by
      exact Evaluates.compare
        (Evaluates.call (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getSubset) .nil)) counted)
        (Evaluates.lookup getK) (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
    refine ⟨allocated ++ extra, ?_⟩
    simp only [good, member, decide_true, Bool.true_and]
    apply Evaluates.boolean_next (flag := true) (by simpa only [member, decide_true] using tested) rfl rfl
    apply Evaluates.boolean_last (flag := decide (k ≤ (ProjectEulerStatements.P51.primeFamilySize n (replace_at.positions indices) : Int)))
    · simpa only [List.append_assoc] using compared
    · rfl
  · refine ⟨allocated, ?_⟩
    simp only [good, member, decide_false, Bool.false_and]
    exact Evaluates.boolean_stop (flag := false) (by simpa only [member, decide_false] using tested) rfl rfl

private theorem replaceAt_reverse (items indices : List Nat) (digit : Nat) :
    ProjectEulerStatements.P51.replaceAt items indices.reverse digit = ProjectEulerStatements.P51.replaceAt items indices digit := by
  have loop (items : List Nat) (position : Nat) :
      ProjectEulerStatements.P51.replaceAt.go indices.reverse digit items position =
      ProjectEulerStatements.P51.replaceAt.go indices digit items position := by
    induction items generalizing position with
    | nil => rfl
    | cons head tail ih => simp [ProjectEulerStatements.P51.replaceAt.go, List.mem_reverse, ih]
  exact loop items 0

private theorem family_reverse (n : Nat) (indices : List Nat) :
    ProjectEulerStatements.P51.familyNumbers n indices.reverse = ProjectEulerStatements.P51.familyNumbers n indices := by
  simp only [ProjectEulerStatements.P51.familyNumbers, replaceAt_reverse]

private theorem good_natural (k : Int) (n : Nat) (indices : List Nat) :
    good k n (indices.reverse.map Int.ofNat) =
      (decide (n ∈ ProjectEulerStatements.P51.familyNumbers n indices) &&
        decide (k.toNat ≤ ProjectEulerStatements.P51.primeFamilySize n indices)) := by
  have ordered : k ≤ (ProjectEulerStatements.P51.primeFamilySize n indices : Int) ↔
      k.toNat ≤ ProjectEulerStatements.P51.primeFamilySize n indices := by omega
  have sizeReverse : ProjectEulerStatements.P51.primeFamilySize n indices.reverse =
      ProjectEulerStatements.P51.primeFamilySize n indices := by
    simp only [ProjectEulerStatements.P51.primeFamilySize, family_reverse]
  simp only [good, familyValues, replace_at.positions_natural, family_reverse, sizeReverse, ordered]


private def indices (n : Nat) : List Int := (List.range (Nat.digits 10 n).length).map Int.ofNat
private def rowValues (n : Nat) : List (List Int) := sublists.values (indices n)
private def lengthExpression : Expr := .builtinCall .len [.call (.name "digits_le") [.name "n"]]
private def rangeExpression : Expr := .listComp (.name "$formalsw.range.item")
  [("$formalsw.range.item", .call (.name "range") [lengthExpression], [])]
private def iterable : Expr := .call (.name "sublists") [rangeExpression]

private theorem iterator_result (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n)) :
    ∃ extra address addresses, Evaluates program env iterable heap (.ref address) (heap ++ extra) ∧
      (heap ++ extra)[address]? = some (.list (sublists.refs addresses)) ∧
      sublists.Rows (heap ++ extra) [address] addresses (rowValues n) := by
  let digitsHeap := heap ++ [.list (naturals (Nat.digits 10 n))]
  have length : Evaluates program env lengthExpression heap (number (Nat.digits 10 n).length) digitsHeap := by
    apply Evaluates.builtin (.cons (Evaluates.call (.cons (Evaluates.lookup getN) .nil)
      ((common.digits_le.decimal n heap).extend common_extension)) .nil)
    simp [primitive, Mutable.length, naturals, digitsHeap]
  obtain ⟨rangeGarbage, collected⟩ := range_map_effectful program "$formalsw.range.item" (.name "$formalsw.range.item")
    (fun (n : Nat) => number n)
    (fun _ _ _ lookup => ⟨[], by simpa only [List.append_nil] using Evaluates.lookup lookup⟩)
    heap digitsHeap env [lengthExpression] [number (Nat.digits 10 n).length] 0 (Nat.digits 10 n).length (.cons length .nil) (by simp only [Nat.cast_zero, zero_add]; rfl)
  let rangeHeap := working digitsHeap (numbers (indices n)) rangeGarbage
  have rangeEval : Evaluates program env rangeExpression heap (.ref digitsHeap.length) rangeHeap := by
    simpa only [rangeExpression, rangeHeap, indices, numbers, naturals, List.range_eq_range', List.map_map, Function.comp_def] using collected
  obtain ⟨subsetExtra, address, addresses, subsets, found, represented⟩ := sublists.result (indices n) rangeHeap digitsHeap.length (by simp [rangeHeap])
  let extra := .list (naturals (Nat.digits 10 n)) :: .list (numbers (indices n)) :: (rangeGarbage ++ subsetExtra)
  have finalShape : rangeHeap ++ subsetExtra = heap ++ extra := by
    dsimp [rangeHeap, digitsHeap, working, extra]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ⟨extra, address, addresses, ?_, ?_, ?_⟩
  · simpa only [finalShape] using (Evaluates.call (module := program) (env := env) (.cons rangeEval .nil) subsets)
  · simpa only [finalShape] using found
  · simpa only [finalShape] using represented


private def anyBody : List Stmt := comprehensionFilters [.name "s"] (truthBody false element)
private def accepted (k : Int) (n : Nat) (rows : List (List Int)) : Bool :=
  (rows.filter (fun row => !row.isEmpty)).any (good k n)

private theorem any_loop (k : Int) (n : Nat) (allAddresses : List Nat) (sourceAddress : Nat) (remainingRows : List (List Int))
    (heap : Mutable.Heap) (remainingAddresses : List Nat) (position : Nat)
    (suffix : allAddresses.drop position = remainingAddresses)
    (found : heap[sourceAddress]? = some (.list (sublists.refs allAddresses)))
    (represented : sublists.Rows heap [sourceAddress] remainingAddresses remainingRows)
    (env : HeapCalls.Env) (getK : env "k" = some (number k)) (getN : env "n" = some (number n)) :
    ∃ extra, BlockReturns program env
      [.sequenceStepLoop "s" (.ref sourceAddress) position anyBody [], .return (.constant (.bool false))]
      heap (flag (accepted k n remainingRows)) (heap ++ extra) := by
  induction remainingRows generalizing heap remainingAddresses position env with
  | nil =>
      cases remainingAddresses with
      | cons address tail => cases represented
      | nil =>
          refine ⟨[], ?_⟩
          simp only [List.append_nil]
          apply BlockReturns.sequence_done (items := sublists.refs allAddresses)
            (by simp [sequenceValue, Mutable.sequence, found])
          · have missing : allAddresses[position]? = none := by
              simpa [suffix] using (List.head?_drop (l := allAddresses) (i := position)).symm
            simp [sublists.refs, missing]
          · exact BlockReturns.return_value Evaluates.constant
  | cons row tail ih =>
      cases remainingAddresses with
      | nil => cases represented
      | cons address tailAddresses =>
          cases represented with
          | cons headFound tailRows =>
              let bound := setLocal env "s" (.ref address)
              have boundK : bound "k" = some (number k) := by simpa [bound, setLocal] using getK
              have boundN : bound "n" = some (number n) := by simpa [bound, setLocal] using getN
              have selected : allAddresses[position]? = some address := by
                simpa [suffix] using (List.head?_drop (l := allAddresses) (i := position)).symm
              have tailSuffix : allAddresses.drop (position + 1) = tailAddresses := by
                simp [List.drop_add_one_eq_tail_drop, suffix]
              cases row with
              | nil =>
                  obtain ⟨extra, rest⟩ := ih heap tailAddresses (position + 1) tailSuffix found tailRows bound boundK boundN
                  refine ⟨extra, ?_⟩
                  simp only [accepted, List.filter_cons, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false]
                  apply BlockReturns.sequence_step (items := sublists.refs allAddresses) (value := .ref address)
                    (by simp [sequenceValue, Mutable.sequence, found]) (by simp [sublists.refs, selected])
                  apply BlockReturns.branch (flag := false) (Evaluates.lookup (value := .ref address) (by simp [setLocal]))
                    (by simp [Mutable.truth, headFound.2, numbers])
                  simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_or,
                    Bool.false_eq_true, if_false, List.nil_append] using rest
              | cons first digits =>
                  obtain ⟨allocated, tested⟩ := element_result k n (first :: digits) heap address headFound.2 bound boundK boundN
                    (by simp [bound, setLocal])
                  cases yes : good k n (first :: digits) with
                  | true =>
                      refine ⟨allocated, ?_⟩
                      simp only [accepted, List.filter_cons, List.isEmpty_cons, Bool.not_false, if_true, List.any_cons, yes, Bool.true_or]
                      apply BlockReturns.sequence_step (items := sublists.refs allAddresses) (value := .ref address)
                        (by simp [sequenceValue, Mutable.sequence, found]) (by simp [sublists.refs, selected])
                      apply BlockReturns.branch (flag := true) (Evaluates.lookup (value := .ref address) (by simp [setLocal]))
                        (by simp [Mutable.truth, headFound.2, numbers])
                      apply BlockReturns.branch (flag := true) (by simpa only [yes] using tested) rfl
                      exact BlockReturns.return_value Evaluates.constant
                  | false =>
                      obtain ⟨extra, rest⟩ := ih (heap ++ allocated) tailAddresses (position + 1) tailSuffix
                        (prefix_found heap allocated _ _ found) (sublists.Rows.extend tailRows allocated) bound boundK boundN
                      refine ⟨allocated ++ extra, ?_⟩
                      simp only [accepted, List.filter_cons, List.isEmpty_cons, Bool.not_false, if_true, List.any_cons, yes, Bool.false_or]
                      apply BlockReturns.sequence_step (items := sublists.refs allAddresses) (value := .ref address)
                        (by simp [sequenceValue, Mutable.sequence, found]) (by simp [sublists.refs, selected])
                      apply BlockReturns.branch (flag := true) (Evaluates.lookup (value := .ref address) (by simp [setLocal]))
                        (by simp [Mutable.truth, headFound.2, numbers])
                      apply BlockReturns.branch (flag := false) (by simpa only [yes] using tested) rfl
                      simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, Bool.false_or,
                        Bool.false_eq_true, if_false, List.nil_append, List.append_assoc] using rest


private def anyExpression : Expr := .consumeGenerator (.builtinCall .any []) element [(.name "s", iterable, [.name "s"])]

private theorem any_result (k : Int) (n : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getK : env "k" = some (number k)) (getN : env "n" = some (number n)) :
    ∃ extra, Evaluates program env anyExpression heap (flag (accepted k n (rowValues n))) (heap ++ extra) := by
  obtain ⟨allocated, address, addresses, iterator, found, represented⟩ := iterator_result n heap env getN
  let inner := comprehensionTargetsEnv env [(.name "s", iterable, [.name "s"])]
  obtain ⟨extra, scanned⟩ := any_loop k n addresses address (rowValues n) (heap ++ allocated) addresses 0 rfl found represented inner
    (by simpa [inner, comprehensionTargetsEnv, targetLocals] using getK)
    (by simpa [inner, comprehensionTargetsEnv, targetLocals] using getN)
  refine ⟨allocated ++ extra, ?_⟩
  apply Evaluates.truth_generator_sequence (universal := false) (items := sublists.refs addresses)
    (by intros; simp [iterable]) (by intros; simp [iterable]) (by intros; simp [iterable]) iterator
    (by simp [Mutable.sequence, found])
  simpa only [List.append_assoc] using scanned

private theorem accepted_native (k : Int) (n : Nat) :
    accepted k n (rowValues n) =
      (((List.range (Nat.digits 10 n).length).sublists.filter (fun row => row ≠ [])).any
        (fun row => decide (n ∈ ProjectEulerStatements.P51.familyNumbers n row) &&
          decide (k.toNat ≤ ProjectEulerStatements.P51.primeFamilySize n row))) := by
  simp only [accepted, rowValues, indices, sublists.values, List.sublists_map, List.map_map,
    List.any_filter, List.any_map, Function.comp_def]
  apply List.any_congr rfl
  intro row
  rw [← List.map_reverse, good_natural]
  simp only [List.isEmpty_map, List.isEmpty_reverse]
  cases row <;> rfl

private theorem native_value (k : Int) (n : Nat) :
    ProjectEulerStatements.P51.hasPrimeFamily k.toNat n = (decide (Nat.Prime n) && accepted k n (rowValues n)) := by
  rw [accepted_native]
  exact Bool.and_comm _ _

/-- The source short-circuits on primality, skips the empty subset, and tests every other subset in source order. -/
theorem result (k : Int) (n : Nat) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "has_prime_family" [number k, number n] heap
      (flag (ProjectEulerStatements.P51.hasPrimeFamily k.toNat n)) (heap ++ extra) := by
  let env := functionEnv ((findFunctionIn program.body "has_prime_family").getD ([], [])).1
    ((findFunctionIn program.body "has_prime_family").getD ([], [])).2 [number k, number n] []
  have tested : Evaluates program env (.call (.name "is_prime") [.name "n"]) heap (flag (decide (Nat.Prime n))) heap :=
    Evaluates.call (.cons (Evaluates.lookup rfl) .nil) ((common.is_prime.heap_result n heap).extend common_extension)
  by_cases prime : Nat.Prime n
  · obtain ⟨extra, families⟩ := any_result k n heap env rfl rfl
    refine ⟨extra, ?_⟩
    rw [native_value]
    simp only [prime, decide_true, Bool.true_and]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.boolean_next (flag := true) (by simpa only [prime, decide_true] using tested) rfl rfl
    exact Evaluates.boolean_last (flag := accepted k n (rowValues n)) families rfl
  · refine ⟨[], ?_⟩
    rw [native_value]
    simp only [prime, decide_false, Bool.false_and, List.append_nil]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    exact Evaluates.boolean_stop (flag := false) (by simpa only [prime, decide_false] using tested) rfl rfl


/-- Negative candidates short-circuit before decimal conversion; negative thresholds agree with zero. -/
theorem signed_result (k n : Int) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "has_prime_family" [number k, number n] heap
      (flag (ProjectEulerStatements.P51.hasPrimeFamily k.toNat n.toNat)) (heap ++ extra) := by
  by_cases nonnegative : 0 ≤ n
  · lift n to Nat using nonnegative
    simpa only [Int.toNat_natCast] using result k n heap
  · have small : ReturnsValue program "is_prime" [number n] heap (flag false) heap := by
      apply BlockReturns.function rfl rfl
      apply BlockReturns.branch (middle := heap) (flag := true) (value := flag true)
        (Evaluates.compare (middle := heap) (afterRight := heap) (Evaluates.lookup rfl) Evaluates.constant
          (by simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega)) rfl
      exact BlockReturns.return_value Evaluates.constant
    have missing : n.toNat = 0 := by omega
    have rejected : ProjectEulerStatements.P51.hasPrimeFamily k.toNat n.toNat = false := by
      simp only [missing, ProjectEulerStatements.P51.hasPrimeFamily, ProjectEulerStatements.P51.isPrime]
      simp
    refine ⟨[], ?_⟩
    rw [rejected, List.append_nil]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.boolean_stop (flag := false) (truth := rfl) (stop := rfl)
    exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) small

theorem «Returns» (k n : Int) : (HeapCalls.scalarFunction program "has_prime_family" [.int k, .int n]).Returns := by
  obtain ⟨extra, returned⟩ := signed_result k n []
  exact returned.scalar_returns

theorem «Supported» (k n : Int) : (HeapCalls.scalarFunction program "has_prime_family" [.int k, .int n]).Supported :=
  («Returns» k n).supported

end has_prime_family

end data.«project-euler-statements».data.py.project_euler_statements.p51
