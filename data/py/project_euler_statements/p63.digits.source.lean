import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p63.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerSolutions.Lib.PowerfulDigitCounts

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p63
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.PowerfulDigits
private abbrev program := P63Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)

theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 4 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["num_digits", "naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

/-- Digit width comes from the actual digit-list helper, including its fresh allocation. -/
theorem num_digits.result (value base : Nat) (valid : 2 ≤ base) (heap : Mutable.Heap)
    (globals : Mutable.Globals := []) :
    ReturnsValue program "num_digits" [number value, number base] heap
      (number (width base value))
      (heap ++ [.list ((Nat.digits base value).map number)]) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin
    (.cons (Evaluates.call
      (.cons (Evaluates.lookup (by cases globals <;> rfl))
        (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil))
      ((common.digits_le.result value base (by omega) heap globals).extend common_extension)) .nil)
  simp [primitive, Mutable.length, width, number]

end data.«project-euler-statements».data.py.project_euler_statements.p63
