import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».Minimal
import lang.py.FormalSW.SumCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p89.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions RomanNumerals
set_option Elab.async false

abbrev element : Expr := .call (.name "saved_chars") [.name "s"]

/-- The generator retains its input list while each complete normalization allocates private objects. -/
theorem sum_loop (lines remaining : List String) (position : Nat) (suffix : lines.drop position = remaining)
    (heap : Mutable.Heap) (address : Nat) (found : heap[address]? = some (.list (lines.map string)))
    (env : HeapCalls.Env) (initial : Int) (getTotal : env sumAccumulator = some (.scalar (.int initial))) :
    ∃ extra, BlockReturns program env
      [.sequenceStepLoop "s" (.ref address) position (sumBody element []) [], .return (.name sumAccumulator)]
      heap (.scalar (.int (initial + (remaining.map saved).sum))) (heap ++ extra) := by
  induction remaining generalizing position heap env initial with
  | nil =>
      refine ⟨[], ?_⟩
      simp only [List.map_nil, List.sum_nil, Int.add_zero, List.append_nil]
      apply BlockReturns.sequence_done (items := lines.map string)
      · simp [sequenceValue, Mutable.sequence, found]
      · have finished : lines[position]? = none := List.getElem?_eq_none_iff.mpr (List.drop_eq_nil_iff.mp suffix)
        simp [finished]
      · exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | cons head tail ih =>
      have item : lines[position]? = some head := by
        have first := congrArg (fun xs : List String => xs[0]?) suffix
        simpa using first
      have rest : lines.drop (position + 1) = tail := by
        have dropped := congrArg (List.drop 1) suffix
        simpa [List.drop_drop, Nat.add_comm] using dropped
      let bound := setLocal env "s" (string head)
      obtain ⟨extra, counted⟩ := saved_chars.result head heap
      let advanced := setLocal bound sumAccumulator (.scalar (.int (initial + saved head)))
      have retained : (heap ++ extra)[address]? = some (.list (lines.map string)) :=
        HeapCollection.prefix_found heap extra address _ found
      obtain ⟨later, continued⟩ := ih (position + 1) rest (heap ++ extra) retained advanced
        (initial + saved head) (by simp [advanced, setLocal])
      refine ⟨extra ++ later, ?_⟩
      simp only [List.map_cons, List.sum_cons]
      apply BlockReturns.sequence_step (items := lines.map string) (value := string head)
      · simp [sequenceValue, Mutable.sequence, found]
      · simp [item]
      · apply BlockReturns.assign (value := .scalar (.int (initial + saved head))) (middle := heap ++ extra)
        · apply Evaluates.binary (av := .scalar (.int initial)) (bv := .scalar (.int (saved head)))
            (middle := heap) (afterRight := heap ++ extra)
          · exact Evaluates.lookup (by simpa [setLocal, sumAccumulator] using getTotal)
          · exact Evaluates.call (.cons (Evaluates.lookup (by simp [setLocal])) .nil) counted
          · rfl
        · simpa only [sumBody, element, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            Bool.false_or, Bool.false_eq_true, if_false, List.nil_append, Int.add_assoc, List.append_assoc] using continued

/-- The complete reference returns the signed character difference for every list of strings. -/
theorem result (lines : List String) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (lines.map string))) :
    ∃ extra, ReturnsValue program "naive" [.ref address] heap (.scalar (.int (savings lines))) (heap ++ extra) := by
  let entry := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [.ref address] []
  let generator := setLocal (comprehensionEnv entry [("s", .name "lines", [])]) sumAccumulator (.scalar (.int 0))
  obtain ⟨extra, summed⟩ := sum_loop lines lines 0 rfl heap address found generator 0 (by simp [generator, setLocal])
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_sequence (items := lines.map string) (middle := heap) (afterStart := heap)
    (by intros; simp) (Evaluates.lookup rfl)
  · simp [Mutable.sequence, found]
  · exact Evaluates.constant
  · rfl
  · simpa only [Int.zero_add, saved, decoded, characters, savings] using summed

end data.«project-euler-statements».data.py.project_euler_statements.p89.naive
