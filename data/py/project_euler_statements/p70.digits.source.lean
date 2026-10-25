import data.«project-euler-statements».data.py.project_euler_statements.«p70.phi.heap.source»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import ProjectEulerSolutions.Lib.PrimePermutations
import ProjectEulerSolutions.Lib.HeapCollection
import ProjectEulerStatements.Lib.TotientPermutation

/-! The reference's allocated digit lists and their content-based comparison. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p70
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.PrimePermutations
set_option Elab.async false

theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 6++CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["phi", "digits_sorted", "is_permutation", "better", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

def digitObjects (n : Nat) : Mutable.Heap :=
  [.list (numbers (integerDigits n)), .list (numbers (sortedDigits n))]

namespace digits_sorted
/-- Digit conversion and sorting allocate fresh lists, preserving every prior object. -/
theorem result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "digits_sorted" [number n] heap (.ref (heap.length+1))
      (heap++digitObjects n) := by
  let middle := heap++[Mutable.Object.list (numbers (integerDigits n))]
  have converted : ReturnsValue program "digits_le" [number n] heap (.ref heap.length) middle := by
    simpa only [middle, numbers, integerDigits, List.map_map, Function.comp_def] using
      (common.digits_le.decimal n heap).extend common_extension
  have sorted := primitive_sorted_list middle heap.length ((integerDigits n).map Constant.int)
    ((sortedDigits n).map Constant.int)
    (by simp [middle, numbers, number, List.map_map]) (ScalarSort.sort_ints (integerDigits n))
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.builtin
    (.cons (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) converted) .nil)
  simpa [middle, digitObjects, numbers, number, List.map_map, List.append_assoc] using sorted

end digits_sorted

namespace is_permutation
/-- Both sorted lists are compared by contents after all argument allocations have occurred. -/
theorem result (a b : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "is_permutation" [number a, number b] heap
      (flag (ProjectEulerStatements.TotientPermutation.isPermutation a b))
      (heap++digitObjects a++digitObjects b) := by
  change ReturnsValue program "is_permutation" [number a, number b] heap
    (flag (ProjectEulerStatements.P49.isPermutation a b)) (heap ++ digitObjects a ++ digitObjects b)
  rw [← permutation_statement]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.compare (av := .ref (heap.length+1))
    (bv := .ref ((heap++digitObjects a).length+1))
    (middle := heap++digitObjects a) (afterRight := heap++digitObjects a++digitObjects b)
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (digits_sorted.result a heap)
  · exact Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
      (digits_sorted.result b (heap++digitObjects a))
  · apply compare_int_lists (sortedDigits a) (sortedDigits b)
    · simp [digitObjects, numbers, List.append_assoc]
    · simp [digitObjects, numbers, List.append_assoc, Nat.add_assoc]

end is_permutation

end data.«project-euler-statements».data.py.project_euler_statements.p70
