import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».SplitLoop

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

theorem nontrivial (a b : Int) (rest : List Int) (smaller : Smaller (a :: b :: rest))
    (heap : Mutable.Heap) (address : Nat) (globals : Mutable.Globals)
    (input : heap[address]? = some (.tuple (integers (a :: b :: rest)))) :
    Computed (a :: b :: rest) address heap globals := by
  let xs := a :: b :: rest
  let args := ((findFunctionIn program.body "all_results").getD ([], [])).1
  let source := ((findFunctionIn program.body "all_results").getD ([], [])).2
  let entry := functionEnv args source [.ref address] globals
  have getNums : entry "nums" = some (.ref address) := by cases globals <;> rfl
  let initialized := setLocal entry "out" (.ref heap.length)
  have ready : Ready initialized address heap.length := by
    constructor
    · simpa [initialized, setLocal] using getNums
    · simp [initialized, setLocal]
  obtain ⟨values, extra, finalEnv, loop, rows, finalReady⟩ :=
    split_loop xs smaller heap address input 1 (rest.length + 1) (by decide)
      (by simp [xs]; omega) [] [] [] initialized globals .nil ready
  simp only [List.nil_append] at loop rows
  have inputAfter : (working heap [] [])[address]? = some (.tuple (integers xs)) :=
    prefix_found heap [.list []] address _ input
  have lengthAfter : Evaluates program initialized (.builtinCall .len [.name "nums"])
      (working heap [] []) (Heap.number xs.length) (working heap [] []) globals :=
    Evaluates.builtin (.cons (Evaluates.lookup ready.nums) .nil)
      (by simp [HeapCalls.primitive, Mutable.length, inputAfter, integers])
  have traversal : BlockContinues program initialized
      [.forIn (.name "split") (.call (.name "range") [.constant (.int 1), .builtinCall .len [.name "nums"]]) splitBody []]
      (working heap [] []) finalEnv (working heap values extra) globals :=
    BlockContinues.for_range (.cons Evaluates.constant (.cons lengthAfter .nil)) rfl loop
  refine ⟨heap.length, .list values :: extra, Nat.le_refl _, ?_, ?_⟩
  · apply BlockReturns.function rfl rfl
    apply BlockReturns.branch (flag := false) (value := .scalar (.bool false)) (middle := heap)
      (Evaluates.unary (Evaluates.lookup getNums)
        (by simp [HeapCalls.unary, Mutable.truth, input, integers])) rfl
    apply BlockReturns.branch (flag := false) (value := .scalar (.bool false)) (middle := heap)
      (Evaluates.compare
        (Evaluates.builtin (value := Heap.number xs.length) (finalHeap := heap)
          (.cons (Evaluates.lookup getNums) .nil)
          (by simp [HeapCalls.primitive, Mutable.length, input, integers, xs]))
        Evaluates.constant (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, xs]; omega)) rfl
    apply BlockReturns.assign (Evaluates.list .nil)
    exact traversal.returns (BlockReturns.return_value (Evaluates.lookup finalReady.out))
  · refine ⟨values, found heap values extra, ?_⟩
    simpa only [enumeratePairs_step] using rows

/-- Structural recursion on the number of operands proves the complete Python enumeration. -/
theorem result (xs : List Int) (heap : Mutable.Heap) (address : Nat) (globals : Mutable.Globals)
    (input : heap[address]? = some (.tuple (integers xs))) : Computed xs address heap globals := by
  have complete : ∀ xs : List Int, ∀ (heap : Mutable.Heap) (address : Nat) (globals : Mutable.Globals),
      heap[address]? = some (.tuple (integers xs)) → Computed xs address heap globals := by
    intro xs
    refine (measure List.length).wf.induction
      (C := fun xs => ∀ (heap : Mutable.Heap) (address : Nat) (globals : Mutable.Globals),
        heap[address]? = some (.tuple (integers xs)) → Computed xs address heap globals) xs ?_
    intro xs ih heap address globals input
    have smaller : Smaller xs := fun ys smaller heap address globals input =>
      ih ys smaller heap address globals input
    cases xs with
    | nil =>
      have completed := empty heap address globals input
      exact ⟨heap.length, [.list []], Nat.le_refl _, completed.1, by simpa [enumeratePairs] using completed.2⟩
    | cons a tail =>
      cases tail with
      | nil =>
        have completed := singleton heap address a globals input
        exact ⟨heap.length + 1, [Heap.object (a, 1), .list [.ref heap.length]], by omega,
          completed.1, by simpa [enumeratePairs] using completed.2⟩
      | cons b rest => exact nontrivial a b rest smaller heap address globals input
  exact complete xs heap address globals input

/-- The returned ordered list contains precisely the exact rational expression values. -/
theorem values (xs : List Int) (heap : Mutable.Heap) (address : Nat) (globals : Mutable.Globals)
    (input : heap[address]? = some (.tuple (integers xs))) :
    ∃ result extra pairs, heap.length ≤ result ∧
      ReturnsValue program "all_results" [.ref address] heap (.ref result) (heap ++ extra) globals ∧
      Heap.ListFound (heap ++ extra) result pairs ∧ (∀ pair ∈ pairs, 0 < pair.2) ∧
      pairs.map value = ProjectEulerSolutions.ArithmeticExpressions.enumerate (xs.map (fun (n : Int) => (n : Rat))) := by
  obtain ⟨result, extra, fresh, executed, found⟩ := result xs heap address globals input
  exact ⟨result, extra, enumeratePairs xs, fresh, executed, found,
    (enumeratePairs_spec xs).1, (enumeratePairs_spec xs).2⟩

end data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
