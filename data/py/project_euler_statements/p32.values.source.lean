import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p32.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerSolutions.Lib.PandigitalProductPermutations

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p32
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.PandigitalProductSearch
private abbrev program := P32Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev numbers (items : List Nat) : List Mutable.Value := items.map number

theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 3 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["naive", "naive_default"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

theorem of_digits_be.result (items : List Nat) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (numbers items))) :
    ReturnsValue program "of_digits_be" [.ref address] heap (number (value items))
      (heap ++ [.list (numbers items.reverse)]) := by
  have executed := common.of_digits_be.result (items.map (fun n : Nat => (n : Int))) 10 heap address
    (by simpa [numbers, number, List.map_map] using found)
  have naturalValue : ProjectEulerStatements.PositionalDigits.value 10
      ((items.map (fun n : Nat => (n : Int))).reverse) = ((value items : Nat) : Int) := by
    simpa only [value, Nat.cast_ofNat, List.map_reverse] using
      ProjectEulerStatements.PositionalDigits.value_naturals 10 items.reverse
  rw [naturalValue] at executed
  have defaulted := ReturnsValue.with_defaults (supplied := [.ref address]) rfl rfl rfl executed
  simpa only [numbers, number, List.map_reverse, List.map_map] using
    defaulted.extend common_extension

end data.«project-euler-statements».data.py.project_euler_statements.p32
