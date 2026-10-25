import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p51.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import lang.py.FormalSW.ComprehensionCalls
import lang.py.FormalSW.MembershipCalls
import ProjectEulerSolutions.Lib.HeapCollection
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

end data.«project-euler-statements».data.py.project_euler_statements.p51
