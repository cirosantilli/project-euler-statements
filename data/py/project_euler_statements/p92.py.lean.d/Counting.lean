import data.«project-euler-statements».data.py.project_euler_statements.«p92.py.lean.d».Chain
import ProjectEulerSolutions.Lib.DigitSquareCounts

namespace data.«project-euler-statements».data.py.project_euler_statements.p92.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.DigitSquareChains
set_option Elab.async false

abbrev test : Expr := .call (.name "ends_at_89") [.name "n"]
abbrev body : List Stmt := comprehensionFilters [test] (sumBody (.constant (.int 1)) [])

def picked (first count : Nat) : Nat := ((List.range' first count).filter endsAt89).length

theorem scan (stop : Int) (first count total : Nat)
    (length : (stop - (first : Int)).toNat = count)
    (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getTotal : env sumAccumulator = some (number total)) (globals : Mutable.Globals := []) :
    ∃ extra, BlockReturns program env
      [.rangeStepLoop "n" first stop 1 body [], .return (.name sumAccumulator)] heap
      (number (total + picked first count)) (heap ++ extra) globals := by
  induction count generalizing first total heap env with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [picked, List.range'_zero, List.filter_nil, List.length_nil,
        Nat.add_zero, List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let entered := setLocal env "n" (number first)
      have currentTotal : entered sumAccumulator = some (number total) := by
        simpa [entered, setLocal, sumAccumulator] using getTotal
      obtain ⟨before, returned⟩ := ends_at_89.result first heap globals
      have evaluated : Evaluates program entered test heap (.scalar (.bool (endsAt89 first)))
          (heap ++ before) globals :=
        Evaluates.call (.cons (Evaluates.lookup (by simp [entered, setLocal])) .nil) returned
      by_cases chosen : endsAt89 first = true
      · let updated := setLocal entered sumAccumulator (number (total + 1))
        obtain ⟨extra, rest⟩ := ih (first + 1) (total + 1) (by omega) (heap ++ before) updated
          (by simp [updated, setLocal])
        refine ⟨before ++ extra, ?_⟩
        apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
        apply BlockReturns.branch (flag := true) (by simpa only [chosen] using evaluated) rfl
        apply BlockReturns.assign (value := number (total + 1)) (middle := heap ++ before)
        · exact Evaluates.binary (av := number total) (bv := number 1)
            (middle := heap ++ before) (afterRight := heap ++ before)
            (Evaluates.lookup currentTotal) Evaluates.constant
            (by simp [Mutable.binary, scalarBinary, number])
        · simpa [picked, List.range'_succ, chosen, body, comprehensionFilters, sumBody,
            Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            entered, updated, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using rest
      · have rejected : endsAt89 first = false := Bool.eq_false_iff.mpr chosen
        obtain ⟨extra, rest⟩ := ih (first + 1) total (by omega) (heap ++ before) entered currentTotal
        refine ⟨before ++ extra, ?_⟩
        apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
        apply BlockReturns.branch (flag := false) (by simpa only [rejected] using evaluated) rfl
        simpa [picked, List.range'_succ, rejected, body, comprehensionFilters, sumBody,
          Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          entered, List.append_assoc] using rest

/-- The complete lazy filtered sum covers every positive start below the supplied signed bound. -/
theorem result (limit : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "naive" [.scalar (.int limit)] heap
      (number (count limit)) (heap ++ extra) globals := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let source := ((findFunctionIn program.body "naive").getD ([], [])).2
  let entry := functionEnv args source [.scalar (.int limit)] globals
  let generators : List (String × Expr × List Expr) :=
    [("n", .call (.name "range") [.constant (.int 1), .name "limit_exclusive"], [test])]
  let summed := setLocal (comprehensionEnv entry generators) sumAccumulator (number 0)
  obtain ⟨extra, scanned⟩ := scan limit 1 (limit - 1).toNat 0 rfl heap summed
    (by cases globals <;> rfl) globals
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range (middle := heap) (afterStart := heap)
    (values := [number 1, .scalar (.int limit)])
  · exact .cons Evaluates.constant (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil)
  · rfl
  · exact Evaluates.constant
  · rfl
  · simpa only [summed, generators, body, picked, Nat.zero_add, count] using scanned

end data.«project-euler-statements».data.py.project_euler_statements.p92.naive
