import data.«project-euler-statements».data.py.project_euler_statements.«p88.py.lean.d».ScanStep

namespace data.«project-euler-statements».data.py.project_euler_statements.p88.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.ProductSumNumbers
set_option Elab.async false

/-- Structural induction follows the remaining table entries, including repeated minima. -/
theorem scan_loop (limit tableAddress : Nat) (best : List Nat) (remaining : List Nat)
    (bounded : ∀ value ∈ remaining, value ≤ limit)
    (base : Mutable.Heap) (found : base[tableAddress]? = some (.list (encode best)))
    (index : Nat) (indexBound : index ≤ best.length) (suffix : best.drop index = remaining)
    (visited : Finset Nat) (env : HeapCalls.Env)
    (ready : ScanLocals env limit tableAddress base.length visited) :
    ∃ finalEnv,
      BlockContinues program env [.rangeStepLoop "k" index best.length 1 scanBody []]
        (scanHeap base limit visited) finalEnv (scanHeap base limit (visited ∪ remaining.toFinset)) ∧
      ScanLocals finalEnv limit tableAddress base.length (visited ∪ remaining.toFinset) := by
  induction remaining generalizing index visited env with
  | nil =>
      have exhausted : best.length ≤ index := List.drop_eq_nil_iff.mp suffix
      refine ⟨env, ?_, ?_⟩
      · simpa using (BlockContinues.range_done
          (by simp [Calls.rangeContinues]; omega) BlockContinues.nil :
          BlockContinues program env [.rangeStepLoop "k" index best.length 1 scanBody []]
            (scanHeap base limit visited) env (scanHeap base limit visited))
      · simpa using ready
  | cons value rest ih =>
      have inside : index < best.length := by
        have lengths := congrArg List.length suffix
        simp only [List.length_drop, List.length_cons] at lengths
        omega
      have lookup : best[index]? = some value := by
        have head := congrArg (fun xs : List Nat => xs[0]?) suffix
        simpa using head
      have tail : best.drop (index + 1) = rest := by
        have dropped := congrArg (List.drop 1) suffix
        simpa [List.drop_drop, Nat.add_comm] using dropped
      let boundEnv := setLocal env "k" (number index)
      have boundReady : ScanLocals boundEnv limit tableAddress base.length visited :=
        ⟨by simpa [boundEnv, setLocal] using ready.bound,
          by simpa [boundEnv, setLocal] using ready.best,
          by simpa [boundEnv, setLocal] using ready.seen,
          by simpa [boundEnv, setLocal] using ready.total⟩
      have stepped := scan_step limit index value tableAddress best lookup (bounded value (by simp))
        base found visited boundEnv boundReady (by simp [boundEnv, setLocal])
      obtain ⟨finalEnv, continued, finalReady⟩ := ih (fun v mem => bounded v (by simp [mem]))
        (index + 1) (by omega) tail (insert value visited) (collectedEnv boundEnv value visited)
        (boundReady.collected value)
      have same : insert value visited ∪ rest.toFinset = visited ∪ (value :: rest).toFinset := by
        ext n
        simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
        tauto
      refine ⟨finalEnv, ?_, same ▸ finalReady⟩
      rw [← same]
      apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa only [Calls.loopContinuation, show Calls.loopControl scanBody = false from rfl, if_false,
        Int.natCast_add, Int.natCast_one] using stepped.append continued

/-- The actual reference for-loop returns the distinct sum of the complete minima table. -/
theorem scan_result (maxSize : Nat) (large : 2 ≤ maxSize) (tableAddress : Nat)
    (base : Mutable.Heap) (found : base[tableAddress]? = some (.list (encode (table maxSize))))
    (env : HeapCalls.Env) (ready : ScanLocals env (2 * maxSize) tableAddress base.length ∅)
    (getMax : env "k_max" = some (number maxSize)) :
    ∃ finalEnv,
      BlockContinues program env [code[6]'(by decide)] (scanHeap base (2 * maxSize) ∅) finalEnv
        (scanHeap base (2 * maxSize) ((table maxSize).drop 2).toFinset) ∧
      finalEnv "total" = some (number (answer maxSize)) := by
  obtain ⟨finalEnv, ran, finalReady⟩ := scan_loop (2 * maxSize) tableAddress (table maxSize)
    ((table maxSize).drop 2) (suffix_bounded maxSize) base found 2
    (by rw [table_length]; omega) rfl ∅ env ready
  refine ⟨finalEnv, ?_, ?_⟩
  · apply BlockContinues.for_range (values := [number 2, number (maxSize + 1)])
      (middle := scanHeap base (2 * maxSize) ∅)
    · exact .cons Evaluates.constant (.cons (Evaluates.binary (Evaluates.lookup getMax) Evaluates.constant
        (by simp [Mutable.binary, scalarBinary, number])) .nil)
    · rfl
    · simpa only [Finset.empty_union, table_length] using ran
  · have total := finalReady.total
    rw [Finset.empty_union, ← ProjectEulerSolutions.ListEraseDups.sum_eq, answer_table] at total
    exact total

end data.«project-euler-statements».data.py.project_euler_statements.p88.naive
