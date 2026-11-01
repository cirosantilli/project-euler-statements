import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Collect

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

abbrev integers (xs : List Int) := xs.map Heap.number

theorem prefix_slice (heap : Mutable.Heap) (address split : Nat) (xs : List Int)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (input : heap[address]? = some (.tuple (integers xs)))
    (proper : split < xs.length)
    (getNums : env "nums" = some (.ref address)) (getSplit : env "split" = some (Heap.number split)) :
    ∃ result extra, Evaluates program env
      (.subscript (.name "nums") (.slice none (some (.name "split")) none))
      heap (.ref result) (heap ++ extra) globals ∧
      (heap ++ extra)[result]? = some (.tuple (integers (xs.take split))) := by
  obtain ⟨result, extra, allocated, found⟩ := allocate_tuple (integers (xs.take split)) heap
  refine ⟨result, extra, ?_, found⟩
  apply Evaluates.slice (.cons (Evaluates.lookup getNums)
    (.cons Evaluates.constant (.cons (Evaluates.lookup getSplit) (.cons Evaluates.constant .nil))))
  rw [Mutable.getSlice_tuple_prefix heap address (integers xs) split (by simpa using proper) input]
  simpa only [integers, List.map_take] using allocated

theorem suffix_slice (heap : Mutable.Heap) (address split : Nat) (xs : List Int)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (input : heap[address]? = some (.tuple (integers xs)))
    (positive : 0 < split) (within : split ≤ xs.length)
    (getNums : env "nums" = some (.ref address)) (getSplit : env "split" = some (Heap.number split)) :
    ∃ result extra, Evaluates program env
      (.subscript (.name "nums") (.slice (some (.name "split")) none none))
      heap (.ref result) (heap ++ extra) globals ∧
      (heap ++ extra)[result]? = some (.tuple (integers (xs.drop split))) := by
  obtain ⟨result, extra, allocated, found⟩ := allocate_tuple (integers (xs.drop split)) heap
  refine ⟨result, extra, ?_, found⟩
  apply Evaluates.slice (.cons (Evaluates.lookup getNums)
    (.cons (Evaluates.lookup getSplit) (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
  rw [Mutable.getSlice_tuple_suffix heap address (integers xs) split positive (by simpa using within) input]
  simpa only [integers, List.map_drop] using allocated

end data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
