import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Inner
import ProjectEulerSolutions.Lib.RationalEnumeration

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

abbrev innerBody : List Stmt := [.forIn (.name "b") (.name "right") collect []]

abbrev splitBody : List Stmt :=
  [.assign [.name "left"] (.call (.name "all_results")
      [.subscript (.name "nums") (.slice none (some (.name "split")) none)]),
   .assign [.name "right"] (.call (.name "all_results")
      [.subscript (.name "nums") (.slice (some (.name "split")) none none)]),
   .forIn (.name "a") (.name "left") innerBody []]

/-- The loop bodies are those imported from the reference Python source. -/
theorem source_tail : ((findFunctionIn program.body "all_results").getD ([], [])).2.drop 3 =
    [.forIn (.name "split") (.call (.name "range") [.constant (.int 1), .builtinCall .len [.name "nums"]])
      splitBody [], .return (.name "out")] := rfl

/-- Both source loops visit the Cartesian product, retaining its order and multiplicity. -/
theorem outer (base : Mutable.Heap) (leftAddress rightAddress : Nat)
    (leftValues rightValues : List Mutable.Value) (rightPairs : List Pair)
    (differentLeft : base.length ≠ leftAddress) (differentRight : base.length ≠ rightAddress)
    (remaining : List Pair) (pending : List Mutable.Value) (position : Nat)
    (old : List Mutable.Value) (garbage : Mutable.Heap) (pairs : List Pair)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (foundLeft : (working base old garbage)[leftAddress]? = some (.list leftValues))
    (foundRight : (working base old garbage)[rightAddress]? = some (.list rightValues))
    (suffix : leftValues.drop position = pending)
    (rows : Heap.Rows (working base old garbage) old pairs)
    (todo : Heap.Rows (working base old garbage) pending remaining)
    (rightRows : Heap.Rows (working base old garbage) rightValues rightPairs)
    (getOut : env "out" = some (.ref base.length)) (getRight : env "right" = some (.ref rightAddress)) :
    ∃ appended extra finalEnv,
      BlockContinues program env [.sequenceStepLoop "a" (.ref leftAddress) position innerBody []]
        (working base old garbage) finalEnv (working base (old ++ appended) (garbage ++ extra)) globals ∧
      Heap.Rows (working base (old ++ appended) (garbage ++ extra))
        (old ++ appended) (pairs ++ combine remaining rightPairs) ∧
      (∀ name, name ≠ "a" → name ≠ "b" → finalEnv name = env name) := by
  induction remaining generalizing pending position old garbage pairs env with
  | nil =>
    cases todo
    refine ⟨[], [], env, ?_, ?_, fun _ _ _ => rfl⟩
    · simp only [List.append_nil]
      apply BlockContinues.sequence_done (by simp [sequenceValue, Mutable.sequence, foundLeft])
        (items := leftValues) (rest := .nil)
      have atHead := congrArg (fun xs : List Mutable.Value => xs[0]?) suffix
      simpa using atHead
    · simpa [combine] using rows
  | cons a rest ih =>
    obtain ⟨left, pending, rowA, tail, rfl⟩ := List.forall₂_cons_right_iff.mp todo
    let bound := setLocal env "a" left
    obtain ⟨added, extra, after, collected, combined, kept⟩ :=
      inner base rightAddress rightValues differentRight a left rightPairs rightValues 0 old garbage pairs bound globals
        foundRight rfl rows rowA rightRows (by simpa [bound, setLocal] using getOut) (by simp [bound, setLocal])
    have executed : BlockContinues program bound innerBody (working base old garbage) after
        (working base (old ++ added) (garbage ++ extra)) globals := by
      apply BlockContinues.for_sequence (items := rightValues) (by intro expressions impossible; cases impossible)
        (Evaluates.lookup (by simpa [bound, setLocal] using getRight))
        (by simp [Mutable.sequence, foundRight])
      exact collected
    have nextSuffix : leftValues.drop (position + 1) = pending := by
      have dropHead := congrArg List.tail suffix
      simpa only [List.tail_drop, List.tail_cons] using dropHead
    obtain ⟨appended, later, finalEnv, continued, finalRows, unchanged⟩ :=
      ih pending (position + 1) (old ++ added) (garbage ++ extra)
        (pairs ++ rightPairs.flatMap (reference a)) after
        (other_found base old (old ++ added) garbage extra leftAddress (.list leftValues) differentLeft foundLeft)
        (other_found base old (old ++ added) garbage extra rightAddress (.list rightValues) differentRight foundRight)
        nextSuffix combined (Heap.Rows.collector tail (old ++ added) extra) (rightRows.collector (old ++ added) extra)
        (by rw [kept "out" (by decide)]; simpa [bound, setLocal] using getOut)
        (by rw [kept "right" (by decide)]; simpa [bound, setLocal] using getRight)
    refine ⟨added ++ appended, extra ++ later, finalEnv, ?_, ?_, ?_⟩
    · apply BlockContinues.sequence_step (by simp [sequenceValue, Mutable.sequence, foundLeft])
        (items := leftValues) (value := left)
      · have atHead := congrArg (fun xs : List Mutable.Value => xs[0]?) suffix
        simpa using atHead
      · simpa only [innerBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Bool.false_or, Bool.false_eq_true, if_false, List.append_assoc] using executed.append continued
    · simpa only [combine, List.flatMap_cons, List.append_assoc] using finalRows
    · intro name notA notB
      exact (unchanged name notA notB).trans ((kept name notB).trans (by simp [bound, setLocal, notA]))

end data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
