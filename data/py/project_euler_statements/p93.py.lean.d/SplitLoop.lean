import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Split

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

/-- Visit every interior split, appending its complete Cartesian-product results. -/
theorem split_loop (xs : List Int) (smaller : Smaller xs) (base : Mutable.Heap) (input : Nat)
    (source : base[input]? = some (.tuple (integers xs))) (first count : Nat)
    (positive : 0 < first) (length : first + count = xs.length)
    (old : List Mutable.Value) (garbage : Mutable.Heap) (pairs : List Pair)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (rows : Heap.Rows (working base old garbage) old pairs) (ready : Ready env input base.length) :
    ∃ appended extra finalEnv,
      BlockContinues program env [.rangeStepLoop "split" first xs.length 1 splitBody []]
        (working base old garbage) finalEnv (working base (old ++ appended) (garbage ++ extra)) globals ∧
      Heap.Rows (working base (old ++ appended) (garbage ++ extra))
        (old ++ appended) (pairs ++ (List.range' first count).flatMap (atSplit xs)) ∧
      Ready finalEnv input base.length := by
  induction count generalizing first old garbage pairs env with
  | zero =>
    refine ⟨[], [], env, ?_, ?_, ready⟩
    · simp only [List.append_nil]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
    · simpa using rows
  | succ count ih =>
    let bound := setLocal env "split" (Heap.number first)
    have boundReady : Ready bound input base.length := by
      constructor
      · simpa [bound, setLocal] using ready.nums
      · simpa [bound, setLocal] using ready.out
    obtain ⟨added, extra, after, executed, combined, afterReady⟩ :=
      split_result xs smaller base input first source positive (by omega) old garbage pairs bound globals
        rows boundReady (by simp [bound, setLocal])
    obtain ⟨appended, later, finalEnv, continued, finalRows, finalReady⟩ :=
      ih (first + 1) (by omega) (by omega) (old ++ added) (garbage ++ extra)
        (pairs ++ atSplit xs first) after combined afterReady
    refine ⟨added ++ appended, extra ++ later, finalEnv, ?_, ?_, finalReady⟩
    · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
      simpa only [splitBody, innerBody, collect, Calls.loopContinuation, Calls.loopControl,
        Calls.loopControlStmt, Bool.false_or, Bool.false_eq_true, if_false,
        Int.natCast_add, Int.natCast_one, List.append_assoc] using executed.append continued
    · simpa only [List.range'_succ, List.flatMap_cons, List.append_assoc] using finalRows

end data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
