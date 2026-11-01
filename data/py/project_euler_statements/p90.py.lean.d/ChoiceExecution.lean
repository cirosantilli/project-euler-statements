import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».Choices

/-! Complete reference selection execution for arbitrary input lists and signed face counts. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p90.choose_faces
open FormalSW.PyAst HeapCalls ProjectEulerSolutions DigitDice
set_option Elab.async false

def expression : Expr := .listCompTargets (.builtinCall .list [.name "c"])
  [(.name "c", .combinationsIterable [.name "xs", .name "face_count"], [])]

/-- The comprehension acquires its positional snapshot before allocating the result collector. -/
theorem enumeration (count address : Nat) (labels : List Nat) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (labels.map number)))
    (getInput : env "xs" = some (.ref address)) (getCount : env "face_count" = some (number count)) :
    ∃ (output : List Row) (extra : Mutable.Heap), output.map Row.labels = choices count labels ∧
      Evaluates program env expression heap (.ref heap.length)
        (HeapCollection.working heap (output.map Row.reference) extra) globals ∧
      ∀ row ∈ output, row.Valid (HeapCollection.working heap (output.map Row.reference) extra) := by
  obtain ⟨output, extra, finalEnv, models, collected, valid⟩ :=
    collect (choices count labels) heap [] []
      (comprehensionTargetsEnv env [(.name "c", .combinationsIterable [.name "xs", .name "face_count"], [])]) globals
  refine ⟨output, extra, models, ?_, ?_⟩
  · apply Evaluates.list_comp_targets_combinations
      (.cons (Evaluates.lookup getInput) (.cons (Evaluates.lookup getCount) .nil))
      (rows := captured (choices count labels)) (middle := heap) (finalEnv := finalEnv)
    · simpa only [captured, choices_rows, Combinations.rows_map, List.map_map, Function.comp_def] using
        combinationRows_list heap address count (labels.map number) found
    · simpa only [HeapCollection.working, List.nil_append] using collected
  · intro row mem
    simpa only [List.nil_append] using (valid row mem).2

private theorem guard (count : Int) (labels : List Nat) (address : Nat)
    (env : HeapCalls.Env) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (found : heap[address]? = some (.list (labels.map number)))
    (getInput : env "xs" = some (.ref address)) (getCount : env "face_count" = some (.scalar (.int count))) :
    Evaluates program env (.boolOp .or [
      .compare (.name "face_count") [(.lt, .constant (.int 0))],
      .compare (.name "face_count") [(.gt, .builtinCall .len [.name "xs"])]]) heap
      (.scalar (.bool (decide (count < 0 ∨ (labels.length : Int) < count)))) heap globals := by
  have length : Evaluates program env (.builtinCall .len [.name "xs"]) heap (number labels.length) heap globals := by
    apply Evaluates.builtin (.cons (Evaluates.lookup getInput) .nil)
    simp [primitive, Mutable.length, found, number]
  have below : Evaluates program env (.compare (.name "face_count") [(.lt, .constant (.int 0))])
      heap (.scalar (.bool (decide (count < 0)))) heap globals :=
    Evaluates.compare (Evaluates.lookup getCount) Evaluates.constant rfl
  have above : Evaluates program env (.compare (.name "face_count") [(.gt, .builtinCall .len [.name "xs"])])
      heap (.scalar (.bool (decide ((labels.length : Int) < count)))) heap globals :=
    Evaluates.compare (Evaluates.lookup getCount) length rfl
  by_cases negative : count < 0
  · simpa only [negative, true_or, decide_true] using
      Evaluates.boolean_stop (op := BoolOp.or)
        (rest := [.compare (.name "face_count") [(.gt, .builtinCall .len [.name "xs"])]])
        (by simpa only [negative, decide_true] using below) rfl rfl
  · apply Evaluates.boolean_next (flag := false)
      (by simpa only [negative, decide_false] using below) rfl rfl
    simpa only [negative, false_or] using Evaluates.boolean_last above rfl

/-- Impossible selection sizes return a fresh empty list, using the actual pool length. -/
theorem invalid (count : Int) (labels : List Nat) (address : Nat) (heap : Mutable.Heap)
    (globals : Mutable.Globals) (found : heap[address]? = some (.list (labels.map number)))
    (impossible : count < 0 ∨ (labels.length : Int) < count) :
    ReturnsValue program "choose_faces" [.ref address, .scalar (.int count)] heap (.ref heap.length)
      (heap ++ [.list []]) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.branch (flag := true)
    (guard count labels address _ heap globals found (by cases globals <;> rfl) (by cases globals <;> rfl))
    (by simp only [impossible, decide_true]; rfl)
  exact BlockReturns.return_value (Evaluates.list .nil)

/-- Every nonnegative selection size matches the full positional model, including oversized requests. -/
theorem result (count address : Nat) (labels : List Nat) (heap : Mutable.Heap)
    (globals : Mutable.Globals) (found : heap[address]? = some (.list (labels.map number))) :
    ∃ (output : List Row) (extra : Mutable.Heap), output.map Row.labels = choices count labels ∧
      ReturnsValue program "choose_faces" [.ref address, number count] heap (.ref heap.length)
        (HeapCollection.working heap (output.map Row.reference) extra) globals ∧
      ∀ row ∈ output, row.Valid (HeapCollection.working heap (output.map Row.reference) extra) := by
  by_cases bounded : count ≤ labels.length
  · let args := ((findFunctionIn program.body "choose_faces").getD ([], [])).1
    let source := ((findFunctionIn program.body "choose_faces").getD ([], [])).2
    let env := functionEnv args source [.ref address, number count] globals
    have getInput : env "xs" = some (.ref address) := by cases globals <;> rfl
    have getCount : env "face_count" = some (number count) := by cases globals <;> rfl
    obtain ⟨output, extra, models, evaluated, valid⟩ := enumeration count address labels heap env globals found getInput getCount
    refine ⟨output, extra, models, ?_, valid⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.branch (flag := false) (guard count labels address env heap globals found getInput getCount)
      (by have notBad : ¬ ((count : Int) < 0 ∨ (labels.length : Int) < count) := by omega
          simp only [notBad, decide_false]; rfl)
    exact BlockReturns.return_value evaluated
  · refine ⟨[], [], ?_, invalid count labels address heap globals found (Or.inr (by omega)), by simp⟩
    simp [choices_too_large count labels (by omega)]

/-- Signed counts retain the source's rejection of negative sizes without any search bound. -/
theorem signed_result (count : Int) (address : Nat) (labels : List Nat) (heap : Mutable.Heap)
    (globals : Mutable.Globals) (found : heap[address]? = some (.list (labels.map number))) :
    ∃ (output : List Row) (extra : Mutable.Heap), output.map Row.labels = (if count < 0 then [] else choices count.toNat labels) ∧
      ReturnsValue program "choose_faces" [.ref address, .scalar (.int count)] heap (.ref heap.length)
        (HeapCollection.working heap (output.map Row.reference) extra) globals ∧
      ∀ row ∈ output, row.Valid (HeapCollection.working heap (output.map Row.reference) extra) := by
  by_cases negative : count < 0
  · refine ⟨[], [], by simp [negative], invalid count labels address heap globals found (Or.inl negative), by simp⟩
  · have cast : (count.toNat : Int) = count := by omega
    simpa only [negative, ↓reduceIte, number, cast] using
      result count.toNat address labels heap globals found

end data.«project-euler-statements».data.py.project_euler_statements.p90.choose_faces
