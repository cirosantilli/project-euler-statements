import data.«project-euler-statements».data.py.project_euler_statements.«p70.step.source»

/-! The complete finite reference scan computes the least totient-permutation ratio minimizer. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p70
open FormalSW.PyAst HeapCalls ProjectEulerStatements TotientPermutation
set_option Elab.async false

def scanObjects (first count : Nat) : Mutable.Heap :=
  (List.range' first count).flatMap candidateObjects

theorem loop_continuation_source (next : Stmt) : Calls.loopContinuation loopBody next = next := rfl

/-- The increasing range folds the same strict update, retaining all allocated digit lists. -/
theorem loop_result (first count stop best : Nat) (length : first + count = stop)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (getBest : env "best" = some (number best)) :
    BlockReturns program env
      [.rangeStepLoop "n" first stop 1 loopBody [], .return (.name "best")]
      heap (number ((List.range' first count).foldl visit best : Nat))
      (heap ++ scanObjects first count) := by
  induction count generalizing first best heap env with
  | zero =>
      simp only [List.range'_zero, List.foldl_nil, scanObjects, List.flatMap_nil, List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getBest)
  | succ count ih =>
      let indexed := setLocal env "n" (number first)
      obtain ⟨nextEnv, stepped, nextBest⟩ := candidate_step first best heap indexed rfl
        (by simpa [indexed, setLocal] using getBest)
      have continued := ih (first + 1) (visit best first) (by omega)
        (heap ++ candidateObjects first) nextEnv nextBest
      apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      rw [loop_continuation_source]
      simpa only [List.range'_succ, List.foldl_cons, scanObjects, List.flatMap_cons,
        List.append_assoc, Int.natCast_add, Int.natCast_one] using stepped.returns continued

/-- Every signed bound terminates and returns the specified least minimizer, or zero for absence. -/
theorem naive.result (limit : Int) (heap : Mutable.Heap) :
    ReturnsValue program "naive" [number limit] heap (number (TotientPermutation.result limit))
      (heap ++ scanObjects 0 (limit + 1).toNat) := by
  let env := setLocal (HeapCalls.argumentEnv naiveArgs [number limit]) "best" (number 0)
  apply BlockReturns.function naive_function_source rfl
  rw [naive_code_source]
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_range (values := [number (limit + 1)])
    (start := 0) (stop := limit + 1) (stride := 1) (middle := heap)
    (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant
      (by simp [Mutable.binary, scalarBinary])) .nil) rfl
  by_cases negative : limit < 0
  · have clipped : limit.toNat = 0 := by omega
    have empty : (limit + 1).toNat = 0 := by omega
    simp only [TotientPermutation.result, clipped, bestUpTo, empty, scanObjects,
      List.range'_zero, List.flatMap_nil, List.append_nil]
    apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup rfl)
  · have cast : (limit.toNat : Int) = limit := Int.toNat_of_nonneg (by omega)
    have count : (limit + 1).toNat = limit.toNat + 1 := by omega
    have scanned := loop_result 0 (limit.toNat + 1) (limit.toNat + 1) 0 (by omega) heap env rfl
    simpa only [count, ← List.range_eq_range', fold_range_best, TotientPermutation.result,
      Int.natCast_zero, Int.natCast_add, Int.natCast_one, cast] using scanned

end data.«project-euler-statements».data.py.project_euler_statements.p70
