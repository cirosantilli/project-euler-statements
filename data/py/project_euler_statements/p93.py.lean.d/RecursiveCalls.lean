import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Base
import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Outer

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
set_option Elab.async false

/-- Every call returns a fresh list and preserves its caller's objects. -/
def Computed (xs : List Int) (address : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals) : Prop :=
  ∃ result extra, heap.length ≤ result ∧
    ReturnsValue program "all_results" [.ref address] heap (.ref result) (heap ++ extra) globals ∧
    Heap.ListFound (heap ++ extra) result (enumeratePairs xs)

abbrev Smaller (xs : List Int) :=
  ∀ ys : List Int, ys.length < xs.length → ∀ (heap : Mutable.Heap) (address : Nat) (globals : Mutable.Globals),
    heap[address]? = some (.tuple (integers ys)) → Computed ys address heap globals

theorem prefix_call (xs : List Int) (smaller : Smaller xs) (heap : Mutable.Heap) (address split : Nat)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (input : heap[address]? = some (.tuple (integers xs))) (proper : split < xs.length)
    (getNums : env "nums" = some (.ref address)) (getSplit : env "split" = some (Heap.number split)) :
    ∃ result extra, heap.length ≤ result ∧
      Evaluates program env (.call (.name "all_results")
        [.subscript (.name "nums") (.slice none (some (.name "split")) none)])
        heap (.ref result) (heap ++ extra) globals ∧
      Heap.ListFound (heap ++ extra) result (enumeratePairs (xs.take split)) := by
  obtain ⟨slice, allocated, sliced, found⟩ := prefix_slice heap address split xs env globals input proper getNums getSplit
  obtain ⟨result, extra, fresh, called, results⟩ :=
    smaller (xs.take split) (by simp only [List.length_take]; omega) (heap ++ allocated) slice globals found
  refine ⟨result, allocated ++ extra, ?_, ?_, ?_⟩
  · simp only [List.length_append] at fresh
    omega
  · simpa only [List.append_assoc] using Evaluates.call (.cons sliced .nil) called
  · simpa only [List.append_assoc] using results

theorem suffix_call (xs : List Int) (smaller : Smaller xs) (heap : Mutable.Heap) (address split : Nat)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (input : heap[address]? = some (.tuple (integers xs))) (positive : 0 < split) (proper : split < xs.length)
    (getNums : env "nums" = some (.ref address)) (getSplit : env "split" = some (Heap.number split)) :
    ∃ result extra, heap.length ≤ result ∧
      Evaluates program env (.call (.name "all_results")
        [.subscript (.name "nums") (.slice (some (.name "split")) none none)])
        heap (.ref result) (heap ++ extra) globals ∧
      Heap.ListFound (heap ++ extra) result (enumeratePairs (xs.drop split)) := by
  obtain ⟨slice, allocated, sliced, found⟩ :=
    suffix_slice heap address split xs env globals input positive (Nat.le_of_lt proper) getNums getSplit
  obtain ⟨result, extra, fresh, called, results⟩ :=
    smaller (xs.drop split) (by simp only [List.length_drop]; omega) (heap ++ allocated) slice globals found
  refine ⟨result, allocated ++ extra, ?_, ?_, ?_⟩
  · simp only [List.length_append] at fresh
    omega
  · simpa only [List.append_assoc] using Evaluates.call (.cons sliced .nil) called
  · simpa only [List.append_assoc] using results

end data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
