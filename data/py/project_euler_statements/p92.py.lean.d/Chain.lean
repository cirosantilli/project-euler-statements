import data.«project-euler-statements».data.py.project_euler_statements.«p92.py.lean.d».Guard

namespace data.«project-euler-statements».data.py.project_euler_statements.p92.ends_at_89
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.DigitSquareChains
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

abbrev body : List Stmt :=
  [.expr (.call (.attribute (.name "seen") "append") [.name "x"]),
    .assign [.name "x"] (.call (.name "next_term") [.name "x"])]
abbrev loop : Stmt := .whileDo condition body []
abbrev finish : Stmt := .return (.compare (.name "x") [(.eq, .constant (.int 89))])

theorem loop_result {current : Nat} {seen : List Nat} {answer : Bool}
    (trace : ReferenceTrace current seen answer) (caller garbage : Mutable.Heap)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getX : env "x" = some (number current)) (getSeen : env "seen" = some (.ref caller.length)) :
    ∃ finalSeen finalGarbage, BlockReturns program env [loop, finish] (state caller seen garbage)
      (.scalar (.bool answer)) (state caller finalSeen finalGarbage) globals := by
  induction trace generalizing garbage env with
  | @done current seen stopped =>
      have flag : active current seen = false := by
        rcases stopped with one | target | repeated <;> simp [active, *]
      refine ⟨seen, garbage ++ [endpoints], ?_⟩
      apply BlockReturns.while_loop (flag := false)
        (guard_result current seen caller garbage env globals getX getSeen)
        (by rw [flag]; rfl)
      apply BlockReturns.return_value
      exact Evaluates.compare (Evaluates.lookup getX) Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega)
  | @step current seen answer notOne notTarget fresh trace ih =>
      let afterTest := state caller seen (garbage ++ [endpoints])
      let afterAppend := state caller (seen ++ [current]) (garbage ++ [endpoints])
      let afterCall := garbage ++ [endpoints] ++ [.list (digits current)]
      let updated := setLocal env "x" (number (nextTerm current))
      obtain ⟨finalSeen, finalGarbage, rest⟩ := ih afterCall updated
        (by simp [updated, setLocal]) (by simpa [updated, setLocal] using getSeen)
      refine ⟨finalSeen, finalGarbage, ?_⟩
      apply BlockReturns.while_loop (flag := true)
        (guard_result current seen caller garbage env globals getX getSeen)
        (by simp [active, notOne, notTarget, fresh, Mutable.truth, scalarTruth])
      apply BlockReturns.discard (middle := afterAppend)
      · have appended := Evaluates.append (module := program) (globals := globals)
          (heap := afterTest) (Evaluates.lookup getSeen) (found caller (seen.map number) (garbage ++ [endpoints]))
          (Evaluates.lookup getX) (found caller (seen.map number) (garbage ++ [endpoints]))
        simpa only [afterTest, afterAppend, state, store, List.map_append, List.map_singleton] using appended
      · apply BlockReturns.assign (value := number (nextTerm current))
          (middle := state caller (seen ++ [current]) afterCall)
        · have converted := next_term.result current afterAppend globals
          rw [ProjectEulerSolutions.HeapCollection.append] at converted
          exact Evaluates.call (.cons (Evaluates.lookup getX) .nil) converted
        · simpa only [loop, body, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            Bool.false_or, Bool.false_eq_true, if_false, List.nil_append, List.cons_append, List.singleton_append]
            using rest

/-- Complete reference chain execution preserves every caller object and has no iteration cutoff. -/
theorem result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "ends_at_89" [number n] heap
      (.scalar (.bool (endsAt89 n))) (heap ++ extra) globals := by
  let args := ((findFunctionIn program.body "ends_at_89").getD ([], [])).1
  let source := ((findFunctionIn program.body "ends_at_89").getD ([], [])).2
  let entry := functionEnv args source [number n] globals
  let initialized := setLocal (setLocal entry "x" (number n)) "seen" (.ref heap.length)
  obtain ⟨finalSeen, finalGarbage, executed⟩ := loop_result (initial_reference_trace n) heap []
    initialized globals (by simp [initialized, setLocal]) (by simp [initialized, setLocal])
  refine ⟨.list (finalSeen.map number) :: finalGarbage, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := number n) (Evaluates.lookup (by cases globals <;> rfl))
  apply BlockReturns.assign (Evaluates.list Evaluates.Arguments.nil)
  simpa only [state, working, List.map_nil, List.cons_append, List.nil_append] using executed

end data.«project-euler-statements».data.py.project_euler_statements.p92.ends_at_89
