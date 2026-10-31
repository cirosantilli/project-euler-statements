import data.«project-euler-statements».data.py.project_euler_statements.«p74.chains.source»

/-! The reference's lazy filtered sum counts complete chains for arbitrary signed requests. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p74
open FormalSW.PyAst HeapCalls
set_option Elab.async false

namespace naive

abbrev test : Expr := .compare (.call (.name "chain_len") [.name "n"])
  [(.eq, .name "target")]
abbrev body : List Stmt := comprehensionFilters [test] (sumBody (.constant (.int 1)) [])

def picked (target : Int) (first count : Nat) : Nat :=
  ((List.range' first count).filter
    (fun n => decide ((ProjectEulerStatements.P74.chainLen n : Int) = target))).length

theorem tested (start : Nat) (target : Int) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number start))
    (getTarget : env "target" = some (integer target)) (globals : Mutable.Globals := []) :
    ∃ extra, Evaluates program env test heap
      (.scalar (.bool (decide ((ProjectEulerStatements.P74.chainLen start : Int) = target))))
      (heap ++ extra) globals := by
  obtain ⟨extra, returned⟩ := chain_len.result start heap globals
  refine ⟨extra, ?_⟩
  exact Evaluates.compare (Evaluates.call (.cons (Evaluates.lookup getN) .nil) returned)
    (Evaluates.lookup getTarget) rfl

theorem scan (target stop : Int) (first count total : Nat)
    (length : (stop - (first : Int)).toNat = count)
    (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getTarget : env "target" = some (integer target))
    (getTotal : env sumAccumulator = some (number total)) (globals : Mutable.Globals := []) :
    ∃ extra, BlockReturns program env
      [.rangeStepLoop "n" first stop 1 body [], .return (.name sumAccumulator)] heap
      (number (total + picked target first count)) (heap ++ extra) globals := by
  induction count generalizing first total heap env with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [picked, List.range'_zero, List.filter_nil, List.length_nil,
        Nat.add_zero, List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let entered := setLocal env "n" (number first)
      have captured : entered "target" = some (integer target) := by
        simpa [entered, setLocal] using getTarget
      have currentTotal : entered sumAccumulator = some (number total) := by
        simpa [entered, setLocal, sumAccumulator] using getTotal
      obtain ⟨before, evaluated⟩ := tested first target heap entered (by simp [entered, setLocal])
        captured globals
      by_cases chosen : (ProjectEulerStatements.P74.chainLen first : Int) = target
      · let updated := setLocal entered sumAccumulator (number (total + 1))
        obtain ⟨extra, rest⟩ := ih (first + 1) (total + 1) (by omega) (heap ++ before) updated
          (by simpa [updated, setLocal, sumAccumulator] using captured)
          (by simp [updated, setLocal])
        refine ⟨before ++ extra, ?_⟩
        apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
        apply BlockReturns.branch (flag := true)
          (by simpa only [chosen, decide_true] using evaluated) rfl
        apply BlockReturns.assign (value := number (total + 1)) (middle := heap ++ before)
        · exact Evaluates.binary (av := number total) (bv := number 1)
            (middle := heap ++ before) (afterRight := heap ++ before)
            (Evaluates.lookup currentTotal) Evaluates.constant
            (by simp [Mutable.binary, scalarBinary, number])
        · simpa [picked, List.range'_succ, chosen, body, comprehensionFilters, sumBody,
            Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            entered, updated, List.append_assoc, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using rest
      · obtain ⟨extra, rest⟩ := ih (first + 1) total (by omega) (heap ++ before) entered
          captured currentTotal
        refine ⟨before ++ extra, ?_⟩
        apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
        apply BlockReturns.branch (flag := false)
          (by simpa only [chosen, decide_false] using evaluated) rfl
        simpa [picked, List.range'_succ, chosen, body, comprehensionFilters, sumBody,
          Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          entered, List.append_assoc] using rest

theorem result (limit target : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "naive" [integer limit, integer target] heap
      (integer (ProjectEulerStatements.P74.result limit target)) (heap ++ extra) globals := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let source := ((findFunctionIn program.body "naive").getD ([], [])).2
  let entry := functionEnv args source [integer limit, integer target] globals
  let generators : List (String × Expr × List Expr) :=
    [("n", .call (.name "range") [.constant (.int 1), .name "limit"], [test])]
  let summed := setLocal (comprehensionEnv entry generators) sumAccumulator (number 0)
  obtain ⟨extra, scanned⟩ := scan target limit 1 (limit - 1).toNat 0 (by rfl) heap summed
    (by cases globals <;> rfl) (by cases globals <;> rfl) globals
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range (middle := heap) (afterStart := heap)
    (values := [number 1, integer limit])
  · exact .cons Evaluates.constant (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil)
  · rfl
  · exact Evaluates.constant
  · rfl
  · simpa only [summed, generators, body, picked, Nat.zero_add,
      ProjectEulerStatements.P74.result] using scanned

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p74
