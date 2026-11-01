import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Collect

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

/-- The inner live-list loop collects every operation for one left operand. -/
theorem inner (base : Mutable.Heap) (address : Nat) (values : List Mutable.Value)
    (different : base.length ≠ address) (a : Pair) (left : Mutable.Value)
    (remaining : List Pair) (pending : List Mutable.Value) (position : Nat)
    (old : List Mutable.Value) (garbage : Mutable.Heap) (pairs : List Pair)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (foundList : (working base old garbage)[address]? = some (.list values))
    (suffix : values.drop position = pending)
    (rows : Heap.Rows (working base old garbage) old pairs)
    (rowA : Heap.Row (working base old garbage) left a)
    (todo : Heap.Rows (working base old garbage) pending remaining)
    (getOut : env "out" = some (.ref base.length)) (getA : env "a" = some left) :
    ∃ appended extra finalEnv,
      BlockContinues program env [.sequenceStepLoop "b" (.ref address) position collect []]
        (working base old garbage) finalEnv (working base (old ++ appended) (garbage ++ extra)) globals ∧
      Heap.Rows (working base (old ++ appended) (garbage ++ extra))
        (old ++ appended) (pairs ++ remaining.flatMap (reference a)) ∧
      (∀ name, name ≠ "b" → finalEnv name = env name) := by
  induction remaining generalizing pending position old garbage pairs env with
  | nil =>
    cases todo
    refine ⟨[], [], env, ?_, ?_, fun _ _ => rfl⟩
    · simp only [List.append_nil]
      apply BlockContinues.sequence_done (by simp [sequenceValue, Mutable.sequence, foundList])
        (items := values) (rest := .nil)
      have atHead := congrArg (fun xs : List Mutable.Value => xs[0]?) suffix
      simpa using atHead
    · simpa using rows
  | cons b rest ih =>
    cases todo with
    | cons rowB tail =>
      rename_i right pending
      let bound := setLocal env "b" right
      obtain ⟨added, extra, emitted, collected⟩ := collect_result base old garbage pairs a b left right bound globals
        rows rowA rowB (by simpa [bound, setLocal] using getOut)
        (by simpa [bound, setLocal] using getA) (by simp [bound, setLocal])
      have keptList := other_found base old (old ++ added) garbage extra address (.list values) different foundList
      have nextSuffix : values.drop (position + 1) = pending := by
        have dropHead := congrArg List.tail suffix
        simpa only [List.tail_drop, List.tail_cons] using dropHead
      obtain ⟨appended, later, finalEnv, continued, finalRows, unchanged⟩ :=
        ih pending (position + 1) (old ++ added) (garbage ++ extra) (pairs ++ reference a b) bound
          keptList nextSuffix collected (rowA.collector (old ++ added) extra)
          (Heap.Rows.collector tail (old ++ added) extra)
          (by simpa [bound, setLocal] using getOut) (by simpa [bound, setLocal] using getA)
      refine ⟨added ++ appended, extra ++ later, finalEnv, ?_, ?_, ?_⟩
      · apply BlockContinues.sequence_step (by simp [sequenceValue, Mutable.sequence, foundList])
          (items := values) (value := right)
        · have atHead := congrArg (fun xs : List Mutable.Value => xs[0]?) suffix
          simpa using atHead
        · simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            Bool.false_or, Bool.false_eq_true, if_false, List.append_assoc] using emitted.append continued
      · simpa only [List.flatMap_cons, List.append_assoc] using finalRows
      · intro name notB
        exact (unchanged name notB).trans (by simp [bound, setLocal, notB])

end data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
