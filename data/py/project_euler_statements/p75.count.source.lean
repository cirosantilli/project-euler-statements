import data.«project-euler-statements».data.py.project_euler_statements.«p75.predicates.source»

/-! The reference enumerates both legs lazily, retaining its exact signed subtraction. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p75.count_solutions
open FormalSW.PyAst HeapCalls
open ProjectEulerStatements.PythagoreanPerimeterCounting (triangle)
set_option Elab.async false

abbrev innerBody : List Stmt := comprehensionFilters [test] (sumBody (.constant (.int 1)) [])
abbrev outerBody : List Stmt := sumBody (.constant (.int 1))
  [("b", .call (.name "range") [.binOp (.name "p") .add (.constant (.int 1))], [test])]

def row (p a first count total : Nat) : Nat :=
  (List.range' first count).foldl
    (fun total b => if triangle p a b then total + 1 else total) total

def rows (p first count total : Nat) : Nat :=
  (List.range' first count).foldl (fun total a => row p a 0 (p + 1) total) total

def Stable (before after : HeapCalls.Env) : Prop :=
  ∀ name, name ≠ "b" → name ≠ sumAccumulator → after name = before name

variable {globals : Mutable.Globals}

theorem inner (p a first count total : Nat) (endpoint : first + count = p + 1)
    (heap : Mutable.Heap) (locals : HeapCalls.Env)
    (getP : locals "p" = some (number p)) (getA : locals "a" = some (number a))
    (getTotal : locals sumAccumulator = some (number total)) :
    ∃ finalEnv, BlockContinues program locals
      [.rangeStepLoop "b" first (p + 1) 1 innerBody []] heap finalEnv heap globals ∧
      Stable locals finalEnv ∧
      finalEnv sumAccumulator = some (number (row p a first count total)) := by
  induction count generalizing first total locals with
  | zero =>
      refine ⟨locals, BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil,
        fun _ _ _ => rfl, ?_⟩
      exact getTotal
  | succ count ih =>
      let entered := setLocal locals "b" (number first)
      have currentP : entered "p" = some (number p) := by simpa [entered, setLocal] using getP
      have currentA : entered "a" = some (number a) := by simpa [entered, setLocal] using getA
      have currentTotal : entered sumAccumulator = some (number total) := by
        simpa [entered, setLocal, sumAccumulator] using getTotal
      have checked := tested (globals := globals) p a first heap entered currentP currentA
        (by simp [entered, setLocal])
      by_cases chosen : triangle p a first
      · let updated := setLocal entered sumAccumulator (number (total + 1))
        obtain ⟨finalEnv, rest, stable, totalValue⟩ := ih (first + 1) (total + 1) (by omega) updated
          (by simpa [updated, setLocal, sumAccumulator] using currentP)
          (by simpa [updated, setLocal, sumAccumulator] using currentA)
          (by simp [updated, setLocal])
        refine ⟨finalEnv, ?_, ?_, ?_⟩
        · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
          apply BlockContinues.branch_next (flag := true)
            (by simpa only [chosen, decide_true] using checked) rfl
          have assigned : BlockContinues program entered (sumBody (.constant (.int 1)) [])
              heap updated heap globals := by
            apply BlockContinues.assign
            exact Evaluates.binary (Evaluates.lookup currentTotal) Evaluates.constant
              (by simp [Mutable.binary, scalarBinary, number, integer])
          simpa only [innerBody, comprehensionFilters, sumBody, Calls.loopContinuation,
            Calls.loopControl, Calls.loopControlStmt, Bool.false_eq_true, if_false,
            List.cons_append, List.nil_append, List.append_assoc, Nat.cast_add] using
              assigned.append rest
        · intro name notB notTotal
          exact (stable name notB notTotal).trans
            (by simp [updated, entered, setLocal, notB, notTotal])
        · simpa only [row, List.range'_succ, List.foldl_cons, if_pos chosen] using totalValue
      · obtain ⟨finalEnv, rest, stable, totalValue⟩ := ih (first + 1) total (by omega) entered
          currentP currentA currentTotal
        refine ⟨finalEnv, ?_, ?_, ?_⟩
        · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
          apply BlockContinues.branch_next (flag := false)
            (by simpa only [chosen, decide_false] using checked) rfl
          simpa only [innerBody, comprehensionFilters, sumBody, Calls.loopContinuation,
            Calls.loopControl, Calls.loopControlStmt, Bool.false_eq_true, if_false,
            List.nil_append, Nat.cast_add] using rest
        · intro name notB notTotal
          exact (stable name notB notTotal).trans (by simp [entered, setLocal, notB])
        · simpa only [row, List.range'_succ, List.foldl_cons, if_neg chosen] using totalValue

theorem outer (p first count total : Nat) (endpoint : first + count = p + 1)
    (heap : Mutable.Heap) (locals : HeapCalls.Env)
    (getP : locals "p" = some (number p))
    (getTotal : locals sumAccumulator = some (number total)) :
    ∃ finalEnv, BlockContinues program locals
      [.rangeStepLoop "a" first (p + 1) 1 outerBody []] heap finalEnv heap globals ∧
      finalEnv "p" = some (number p) ∧
      finalEnv sumAccumulator = some (number (rows p first count total)) := by
  induction count generalizing first total locals with
  | zero =>
      exact ⟨locals, BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil,
        getP, getTotal⟩
  | succ count ih =>
      let entered := setLocal locals "a" (number first)
      have currentP : entered "p" = some (number p) := by simpa [entered, setLocal] using getP
      obtain ⟨ready, counted, stable, totalValue⟩ := inner (globals := globals)
        p first 0 (p + 1) total (by omega) heap entered currentP (by simp [entered, setLocal])
        (by simpa [entered, setLocal, sumAccumulator] using getTotal)
      have readyP : ready "p" = some (number p) :=
        (stable "p" (by decide) (by decide)).trans currentP
      obtain ⟨finalEnv, continued, finalP, finalTotal⟩ := ih (first + 1)
        (row p first 0 (p + 1) total) (by omega) ready readyP totalValue
      refine ⟨finalEnv, ?_, finalP, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        have countedSource : BlockContinues program entered outerBody heap ready heap globals := by
          apply BlockContinues.for_range (middle := heap) (values := [number (p + 1)])
            (.cons (Evaluates.binary (Evaluates.lookup currentP) Evaluates.constant
              (by simp [Mutable.binary, scalarBinary, number, integer])) .nil) rfl
          exact counted
        simpa only [outerBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          Bool.false_eq_true, if_false, Nat.cast_add] using countedSource.append continued
      · simpa only [rows, List.range'_succ, List.foldl_cons] using finalTotal

theorem natural_result (p : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "count_solutions" [number p] heap
      (number (ProjectEulerStatements.P75.countSolutions p)) heap globals := by
  let args := ((findFunctionIn program.body "count_solutions").getD ([], [])).1
  let source := ((findFunctionIn program.body "count_solutions").getD ([], [])).2
  let entry := functionEnv args source [number p] globals
  let generators : List (String × Expr × List Expr) :=
    [("a", .call (.name "range") [.binOp (.name "p") .add (.constant (.int 1))], []),
     ("b", .call (.name "range") [.binOp (.name "p") .add (.constant (.int 1))], [test])]
  let ready := setLocal (comprehensionEnv entry generators) sumAccumulator (number 0)
  obtain ⟨finished, walked, _, returned⟩ := outer (globals := globals)
    p 0 (p + 1) 0 (by omega) heap ready (by cases globals <;> rfl) (by rfl)
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.sum_generator_range (middle := heap) (afterStart := heap)
    (values := [number (p + 1)])
    (.cons (Evaluates.binary (Evaluates.lookup (by cases globals <;> rfl)) Evaluates.constant
      (by simp [Mutable.binary, scalarBinary, number, integer])) .nil) rfl Evaluates.constant rfl
  have returnedSource : BlockReturns program finished [.return (.name sumAccumulator)] heap
      (number (rows p 0 (p + 1) 0)) heap globals :=
    BlockReturns.return_value (Evaluates.lookup returned)
  intro anchors stack
  have completed := (walked [.return (.name sumAccumulator)] anchors stack).trans
    (returnedSource anchors stack)
  simpa only [ready, generators, outerBody, rows, row, triangle,
    ProjectEulerStatements.P75.countSolutions, List.range_eq_range'] using completed

/-- Negative perimeters have an empty outer range, and every other call uses natural legs. -/
theorem result (p : Int) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "count_solutions" [integer p] heap
      (number (ProjectEulerStatements.P75.countSolutions p.toNat)) heap globals := by
  by_cases negative : p < 0
  · have empty : p.toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
    have counted : ProjectEulerStatements.P75.countSolutions p.toNat = 0 := by rw [empty]; rfl
    rw [counted]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.sum_generator_range (middle := heap) (afterStart := heap)
      (values := [integer (p + 1)])
      (.cons (Evaluates.binary (Evaluates.lookup (by cases globals <;> rfl))
        Evaluates.constant rfl) .nil) rfl Evaluates.constant rfl
    apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup (by rfl))
  · have same : (p.toNat : Int) = p := Int.toNat_of_nonneg (by omega)
    simpa only [number, same] using natural_result p.toNat heap globals

end data.«project-euler-statements».data.py.project_euler_statements.p75.count_solutions
