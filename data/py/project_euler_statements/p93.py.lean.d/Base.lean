import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Slices

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
set_option Elab.async false

theorem empty (heap : Mutable.Heap) (address : Nat) (globals : Mutable.Globals)
    (input : heap[address]? = some (.tuple [])) :
    ReturnsValue program "all_results" [.ref address] heap (.ref heap.length)
      (heap ++ [.list []]) globals ∧ Heap.ListFound (heap ++ [.list []]) heap.length [] := by
  constructor
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.branch (flag := true) (value := .scalar (.bool true)) (middle := heap)
      (Evaluates.unary (Evaluates.lookup (by cases globals <;> rfl))
        (by simp [HeapCalls.unary, Mutable.truth, input])) rfl
    exact BlockReturns.return_value (Evaluates.list .nil)
  · exact ⟨[], by simp, .nil⟩

theorem singleton (heap : Mutable.Heap) (address : Nat) (n : Int) (globals : Mutable.Globals)
    (input : heap[address]? = some (.tuple [Heap.number n])) :
    ReturnsValue program "all_results" [.ref address] heap (.ref (heap.length + 1))
      (heap ++ [Heap.object (n, 1), .list [.ref heap.length]]) globals ∧
      Heap.ListFound (heap ++ [Heap.object (n, 1), .list [.ref heap.length]]) (heap.length + 1) [(n, 1)] := by
  let args := ((findFunctionIn program.body "all_results").getD ([], [])).1
  let source := ((findFunctionIn program.body "all_results").getD ([], [])).2
  let entry := functionEnv args source [.ref address] globals
  have getNums : entry "nums" = some (.ref address) := by cases globals <;> rfl
  have item : Evaluates program entry (.subscript (.name "nums") (.constant (.int 0)))
      heap (Heap.number n) heap globals := by
    apply Evaluates.subscript (by intros a b c impossible; cases impossible)
      (Evaluates.lookup getNums) Evaluates.constant
    simp [Mutable.getItem, Mutable.index, input, Except.map]
  have pair : Evaluates program entry
      (.tuple [.subscript (.name "nums") (.constant (.int 0)), .constant (.int 1)])
      heap (.ref heap.length) (heap ++ [Heap.object (n, 1)]) globals :=
    Evaluates.tuple (.cons item (.cons Evaluates.constant .nil)) (by simp)
  constructor
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.branch (flag := false) (value := .scalar (.bool false)) (middle := heap)
      (Evaluates.unary (Evaluates.lookup (by cases globals <;> rfl))
        (by simp [HeapCalls.unary, Mutable.truth, input])) rfl
    apply BlockReturns.branch (flag := true) (value := .scalar (.bool true)) (middle := heap)
      (Evaluates.compare
        (Evaluates.builtin (value := Heap.number 1) (finalHeap := heap)
          (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil)
          (by simp [HeapCalls.primitive, Mutable.length, input]))
        Evaluates.constant rfl) rfl
    apply BlockReturns.return_value
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero,
      List.append_assoc, List.singleton_append] using Evaluates.list (.cons pair .nil)
  · refine ⟨[.ref heap.length], by simp, .cons ?_ .nil⟩
    exact ⟨heap.length, rfl, by simp⟩

end data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
