import data.«project-euler-statements».data.py.project_euler_statements.«p79.naive.source»
import lang.py.FormalSW.SetChoiceCalls

/-! Set traversal selects the first validation error in the actual reference call. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

abbrev setValidationEnv (value : Mutable.Value) : HeapCalls.Env :=
  functionEnv naiveArgs naiveBody [value] []

theorem naive_set_failure (heap : Mutable.Heap) (address index : Nat) (items : List Constant)
    (s : String) (choices : ChoiceSchedule)
    (found : heap[address]? = some (.set items)) (selected : items[index]? = some (.string s))
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false) (choice : choices 0 = index) :
    ((SetCalls.call program "naive" [.ref address] heap).run choices).Finishes
      ⟨.error (invalidException s), [], heap ++ [.list []], heap.length⟩ := by
  let env := setValidationEnv (.ref address)
  let bound := setLocal env "checked" (.ref heap.length)
  let after := heap ++ [Mutable.Object.list []]
  have allocated : BlockContinues program env
      [.annAssign (.name "checked") (.subscript (.name "list") (.name "str")) (some (.list []))]
      heap bound after := BlockContinues.annAssign (Evaluates.list .nil)
  have saved : after[address]? = some (.set items) := by
    simpa only [after, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found
  change Finishes (SetCalls.step program heap.length choices)
    ⟨⟨.operation (.call "naive") [.ref address], [], heap⟩, 0⟩ _
  apply SetCalls.Reaches.finishes (SetCalls.Reaches.of_heap
    (show HeapCalls.Reaches program heap.length
      ⟨.operation (.call "naive") [.ref address], [], heap⟩ ⟨.block naiveCode env, [], heap⟩ from .next rfl .refl)
    choices 0)
  rw [naive_source]
  apply (SetCalls.Reaches.of_heap (allocated _ heap.length []) choices 0).finishes
  apply (SetCalls.for_set_name program choices heap.length 0 address after items bound "attempt" "attempts"
    validationBody [] [.return checkedExpression] [] (by rfl) saved).finishes
  apply Finishes.next (SetCalls.select_item program choices heap.length 0 address index after items items (.string s)
    bound "attempt" validationBody [] [.return checkedExpression] [] saved selected choice)
  exact SetCalls.finishes_of_heap (rejected_attempt (setLocal bound "attempt" (.scalar (.string s))) after s
    (by simp [setLocal, text]) invalid _ heap.length []) choices 1

end data.«project-euler-statements».data.py.project_euler_statements.p79
