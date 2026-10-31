import data.«project-euler-statements».data.py.project_euler_statements.«p75.count.source»

/-! The outer lazy sum counts singular perimeters for every signed bound. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p75.naive
open FormalSW.PyAst HeapCalls
set_option Elab.async false

abbrev test : Expr := .compare (.call (.name "count_solutions") [.name "p"])
  [(.eq, .constant (.int 1))]
abbrev body : List Stmt := comprehensionFilters [test] (sumBody (.constant (.int 1)) [])

variable {globals : Mutable.Globals}

theorem tested (p : Nat) (heap : Mutable.Heap) (locals : HeapCalls.Env)
    (getP : locals "p" = some (number p)) :
    Evaluates program locals test heap
      (.scalar (.bool (decide (ProjectEulerStatements.P75.countSolutions p = 1))))
      heap globals := by
  have counted := count_solutions.result (p : Int) heap globals
  simp only [Int.toNat_natCast] at counted
  apply Evaluates.compare (Evaluates.call (.cons (Evaluates.lookup getP) .nil) counted)
    Evaluates.constant
  simp [HeapCalls.compare, scalarCompare, evalCmpOp]

theorem scan (stop : Int) (first count total : Nat)
    (length : (stop - (first : Int)).toNat = count) (heap : Mutable.Heap) (locals : HeapCalls.Env)
    (getTotal : locals sumAccumulator = some (number total)) :
    BlockReturns program locals
      [.rangeStepLoop "p" first stop 1 body [], .return (.name sumAccumulator)] heap
      (number (total + ProjectEulerStatements.P75.picked first count)) heap globals := by
  induction count generalizing first total locals with
  | zero =>
      simp only [ProjectEulerStatements.P75.picked, List.range'_zero, List.filter_nil,
        List.length_nil, Nat.add_zero]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
      exact BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let entered := setLocal locals "p" (number first)
      have currentTotal : entered sumAccumulator = some (number total) := by
        simpa [entered, setLocal, sumAccumulator] using getTotal
      have checked := tested (globals := globals) first heap entered (by simp [entered, setLocal])
      by_cases chosen : ProjectEulerStatements.P75.countSolutions first = 1
      · let updated := setLocal entered sumAccumulator (number (total + 1))
        have rest := ih (first + 1) (total + 1) (by omega) updated (by simp [updated, setLocal])
        apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
        apply BlockReturns.branch (flag := true)
          (by simpa only [chosen, decide_true] using checked) rfl
        apply BlockReturns.assign (value := number (total + 1)) (middle := heap)
        · exact Evaluates.binary (Evaluates.lookup currentTotal) Evaluates.constant
            (by simp [Mutable.binary, scalarBinary, number, integer])
        · simpa [ProjectEulerStatements.P75.picked, List.range'_succ, chosen, body,
            comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt, entered, updated, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using rest
      · have rest := ih (first + 1) total (by omega) entered currentTotal
        apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
        apply BlockReturns.branch (flag := false)
          (by simpa only [chosen, decide_false] using checked) rfl
        simpa [ProjectEulerStatements.P75.picked, List.range'_succ, chosen, body,
          comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
          Calls.loopControlStmt, entered] using rest

theorem result (limit : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "naive" [integer limit] heap
      (integer (ProjectEulerStatements.P75.result limit)) heap globals := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let source := ((findFunctionIn program.body "naive").getD ([], [])).2
  let entry := functionEnv args source [integer limit] globals
  let generators : List (String × Expr × List Expr) :=
    [("p", .call (.name "range") [.binOp (.name "limit") .add (.constant (.int 1))], [test])]
  let ready := setLocal (comprehensionEnv entry generators) sumAccumulator (number 0)
  have walked := scan (globals := globals) (limit + 1) 0 (limit + 1).toNat 0
    (by omega) heap ready (by rfl)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range (middle := heap) (afterStart := heap)
    (values := [integer (limit + 1)])
    (.cons (Evaluates.binary (Evaluates.lookup (by cases globals <;> rfl)) Evaluates.constant rfl)
      .nil) rfl Evaluates.constant rfl
  simpa only [ready, generators, body, Nat.zero_add, ProjectEulerStatements.P75.result] using walked

end data.«project-euler-statements».data.py.project_euler_statements.p75.naive
