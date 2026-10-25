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
end data.«project-euler-statements».data.py.project_euler_statements.p51
