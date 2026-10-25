import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p56.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerSolutions.Lib.PowerDigitSum

namespace data.«project-euler-statements».data.py.project_euler_statements.p56
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false
private abbrev program := P56Ast.module

private theorem common_extension : HeapCalls.Extends program CommonAst.module := by
  apply HeapCalls.Extends.of_classless (classless := rfl)
  change Calls.Extends { body := program.body.take 2 ++ CommonAst.module.body } CommonAst.module
  apply Calls.Extends.prepend
  · intro name member
    change name ∈ ["digit_sum", "naive"] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · intro name member
    change name ∈ ([] : List String) at member
    simp at member

def digitValues (n : Nat) : List Mutable.Value :=
  (Nat.digits 10 n).map (fun (digit : Nat) => .scalar (.int (digit : Int)))

/-- The actual common-helper call allocates one digit list, and the original sum traverses that list. -/
theorem digit_sum.result (n : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals := []) :
    ReturnsValue program "digit_sum" [.scalar (.int n)] heap
      (.scalar (.int (PowerDigitSum.digitSum n))) (heap ++ [.list (digitValues n)]) globals := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  have converted := (common.digits_le.decimal n heap globals).extend common_extension
  have total := PowerDigitSum.integer_digits_sum (Nat.digits 10 n)
  change Evaluates program _ _ heap (.scalar (.int ((Nat.digits 10 n).sum : Int))) _ globals
  rw [← total]
  apply Evaluates.sum_integers (initial := 0)
    (values := (Nat.digits 10 n).map (fun (digit : Nat) => (digit : Int)))
  · exact .cons (Evaluates.call (.cons (Evaluates.lookup (by cases globals <;> rfl)) .nil) converted)
      (.cons Evaluates.constant .nil)
  · simp [Mutable.sequence, digitValues, List.map_map, Function.comp_def]

end data.«project-euler-statements».data.py.project_euler_statements.p56

namespace data.«project-euler-statements».data.py.project_euler_statements.p56
open FormalSW.PyAst

theorem digit_sum.«Returns» (n : Int)
    (condition : Calls.Condition P56Ast.module (fun key => if key = "n" then some (.int n) else none)
      P56Ast.requires_digit_sum_0) :
    (HeapCalls.scalarFunction P56Ast.module "digit_sum" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare condition rfl
  have returned : (HeapCalls.scalarFunction P56Ast.module "digit_sum" [.int (n.toNat : Int)]).Returns :=
    (digit_sum.result n.toNat []).scalar_returns
  simpa only [Int.toNat_of_nonneg nonnegative] using returned

theorem digit_sum.«Supported» (n : Int)
    (condition : Calls.Condition P56Ast.module (fun key => if key = "n" then some (.int n) else none)
      P56Ast.requires_digit_sum_0) :
    (HeapCalls.scalarFunction P56Ast.module "digit_sum" [.int n]).Supported :=
  (digit_sum.«Returns» n condition).supported

end data.«project-euler-statements».data.py.project_euler_statements.p56


namespace data.«project-euler-statements».data.py.project_euler_statements.p56.naive
open FormalSW.PyAst FormalSW.PyAst.HeapCalls
open ProjectEulerSolutions
set_option Elab.async false

private abbrev program := P56Ast.module
private abbrev number (value : Int) : Mutable.Value := .scalar (.int value)
private abbrev flag (value : Bool) : Mutable.Value := .scalar (.bool value)
private abbrev element : Expr := .call (.name "digit_sum") [.binOp (.name "a") .pow (.name "b")]
private abbrev cellBody : List Stmt := extremumBody true element
private abbrev rowBody : List Stmt := [.forIn (.name "b") (.call (.name "range") [.name "n"]) cellBody []]

/-- Before the first item, zero is only the default; every later best is an actually seen integer. -/
private def State (env : HeapCalls.Env) (best : Int) : Prop :=
  ∃ seen : Bool, env extremumBest = some (number best) ∧ env extremumSeen = some (flag seen) ∧
    (seen = false → best = 0) ∧ 0 ≤ best

private theorem State.set_other {env : HeapCalls.Env} {best : Int} (known : State env best)
    (name : String) (value : Mutable.Value) (noBest : extremumBest ≠ name) (noSeen : extremumSeen ≠ name) :
    State (setLocal env name value) best := by
  obtain ⟨seen, getBest, getSeen, unseen, nonnegative⟩ := known
  exact ⟨seen, by simpa [setLocal, noBest] using getBest,
    by simpa [setLocal, noSeen] using getSeen, unseen, nonnegative⟩

/-- A genuine integer candidate uses the extrema consumer's source body, without treating default as an input item. -/
private theorem cell (a b : Nat) (best : Int) (heap : Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getA : env "a" = some (number a)) (getB : env "b" = some (number b)) (known : State env best) :
    ∃ finalEnv, BlockContinues program env cellBody heap finalEnv (heap ++ [.list (digitValues (a^b))]) globals ∧
      State finalEnv (max best (PowerDigitSum.score a b)) ∧
      finalEnv "a" = env "a" ∧ finalEnv "n" = env "n" := by
  have power : Evaluates program env (.binOp (.name "a") .pow (.name "b")) heap (number (a^b)) heap globals := by
    apply Evaluates.binary (Evaluates.lookup getA) (Evaluates.lookup getB)
    simp [Mutable.binary, scalarBinary, number, show ¬ (b : Int) < 0 by omega]
  have scored : Evaluates program env element heap (number (PowerDigitSum.score a b))
      (heap ++ [.list (digitValues (a^b))]) globals :=
    Evaluates.call (.cons power .nil) (digit_sum.result (a^b) heap globals)
  obtain ⟨seen, getBest, getSeen, unseen, nonnegative⟩ := known
  obtain ⟨finalEnv, ran, finalSeen, finalBest, preserved⟩ :=
    BlockContinues.extremum_max_int scored getSeen getBest
  have scoreNonnegative : 0 ≤ PowerDigitSum.score a b := Int.natCast_nonneg _
  have selected : (if seen then max best (PowerDigitSum.score a b) else PowerDigitSum.score a b) =
      max best (PowerDigitSum.score a b) := by
    cases seen with
    | true => rfl
    | false => simp only [Bool.false_eq_true, if_false, unseen rfl, max_eq_right scoreNonnegative]
  refine ⟨finalEnv, ran, ?_, preserved "a" (by decide) (by decide) (by decide),
    preserved "n" (by decide) (by decide) (by decide)⟩
  refine ⟨true, ?_, finalSeen, ?_, le_trans nonnegative (le_max_left _ _)⟩
  · simpa only [selected] using finalBest
  · intro impossible
    cases impossible

private theorem row_loop (length first a : Nat) (stop : Int) (equation : stop = ((first+length : Nat) : Int))
    (best : Int) (heap : Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getA : env "a" = some (number a)) (known : State env best) :
    ∃ finalEnv extra, BlockContinues program env [.rangeStepLoop "b" first stop 1 cellBody []]
      heap finalEnv (heap ++ extra) globals ∧
      State finalEnv (PowerDigitSum.row a (List.range' first length) best) ∧
      finalEnv "a" = some (number a) ∧ finalEnv "n" = env "n" := by
  induction length generalizing first best heap env with
  | zero =>
      refine ⟨env, [], ?_, ?_, getA, rfl⟩
      · simpa only [List.append_nil] using
          (BlockContinues.range_done (module := program) (env := env) (heap := heap) (globals := globals)
            (name := "b") (next := first) (stop := stop) (stride := 1) (body := cellBody) (otherwise := [])
            (by simp [Calls.rangeContinues]; omega) .nil)
      · simpa [PowerDigitSum.row] using known
  | succ length ih =>
      let bound := setLocal env "b" (number first)
      have boundA : bound "a" = some (number a) := by simpa [bound, setLocal] using getA
      have boundState : State bound best := known.set_other "b" (number first) (by decide) (by decide)
      obtain ⟨afterCell, ranCell, cellState, cellA, cellN⟩ := cell a first best heap bound globals boundA rfl boundState
      obtain ⟨finalEnv, restExtra, rest, finalState, finalA, finalN⟩ := ih (first+1) (by omega)
        (max best (PowerDigitSum.score a first)) (heap ++ [.list (digitValues (a^first))]) afterCell
        (cellA.trans boundA) cellState
      refine ⟨finalEnv, [.list (digitValues (a^first))] ++ restExtra, ?_, ?_, finalA, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, show Calls.loopControl cellBody = false from rfl,
          Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one, List.append_assoc] using ranCell.append rest
      · simpa only [PowerDigitSum.row, List.range'_succ, List.foldl_cons] using finalState
      · rw [finalN, cellN]
        simp [bound, setLocal]

private theorem outer_loop (length first width : Nat) (stop : Int)
    (equation : stop = ((first+length : Nat) : Int)) (widthEq : stop = (width : Int))
    (best : Int) (heap : Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getN : env "n" = some (number stop)) (known : State env best) :
    ∃ finalEnv extra, BlockContinues program env [.rangeStepLoop "a" first stop 1 rowBody []]
      heap finalEnv (heap ++ extra) globals ∧
      State finalEnv (PowerDigitSum.scan (List.range width) (List.range' first length) best) ∧
      finalEnv "n" = some (number stop) := by
  induction length generalizing first best heap env with
  | zero =>
      refine ⟨env, [], ?_, ?_, getN⟩
      · simpa only [List.append_nil] using
          (BlockContinues.range_done (module := program) (env := env) (heap := heap) (globals := globals)
            (name := "a") (next := first) (stop := stop) (stride := 1) (body := rowBody) (otherwise := [])
            (by simp [Calls.rangeContinues]; omega) .nil)
      · simpa [PowerDigitSum.scan] using known
  | succ length ih =>
      let bound := setLocal env "a" (number first)
      have boundN : bound "n" = some (number stop) := by simpa [bound, setLocal] using getN
      have boundState : State bound best := known.set_other "a" (number first) (by decide) (by decide)
      obtain ⟨afterRow, rowExtra, inner, rowState, rowA, rowN⟩ :=
        row_loop width 0 first stop (by omega) best heap bound globals rfl boundState
      have rowKnown : State afterRow (PowerDigitSum.row first (List.range width) best) := by
        simpa only [List.range_eq_range'] using rowState
      have ranRow : BlockContinues program bound rowBody heap afterRow (heap ++ rowExtra) globals :=
        BlockContinues.for_range (.cons (Evaluates.lookup boundN) .nil) rfl inner
      obtain ⟨finalEnv, restExtra, rest, finalState, finalN⟩ := ih (first+1) (by omega)
        (PowerDigitSum.row first (List.range width) best) (heap ++ rowExtra) afterRow (rowN.trans boundN) rowKnown
      refine ⟨finalEnv, rowExtra ++ restExtra, ?_, ?_, finalN⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa only [Calls.loopContinuation, show Calls.loopControl rowBody = false from rfl,
          Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one, List.append_assoc] using ranRow.append rest
      · simpa only [PowerDigitSum.scan, List.range'_succ, List.foldl_cons] using finalState

private abbrev params := ((findFunctionIn program.body "naive").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "naive").getD ([], [])).2
private abbrev generators : List (Expr × Expr × List Expr) :=
  [(.name "a", .call (.name "range") [.name "n"], []),
    (.name "b", .call (.name "range") [.name "n"], [])]

/-- The reference's original nested lazy max evaluates every power and digit list, preserving the caller heap. -/
theorem result (limit : Int) (heap : Heap) (globals : Mutable.Globals := []) :
    ∃ extra, ReturnsValue program "naive" [number limit] heap
      (number (PowerDigitSum.maximum limit.toNat)) (heap ++ extra) globals := by
  let env := functionEnv params sourceBody [number limit] globals
  let initial := extremumEnv (comprehensionTargetsEnv env generators) (number 0)
  have getN : env "n" = some (number limit) := by cases globals <;> rfl
  have initialN : initial "n" = some (number limit) := by
    simpa [initial, extremumEnv, setLocal, extremumBest, extremumSeen, comprehensionTargetsEnv, generators, targetLocals] using getN
  have initialState : State initial 0 := by
    refine ⟨false, ?_, ?_, by intro _; rfl, by omega⟩
    · simp [initial, extremumEnv, setLocal]
    · simp [initial, extremumEnv, setLocal, extremumBest, extremumSeen]
  have loopResult : ∃ finalEnv extra, BlockContinues program initial
      [.rangeStepLoop "a" 0 limit 1 rowBody []] heap finalEnv (heap ++ extra) globals ∧
      State finalEnv (PowerDigitSum.maximum limit.toNat) := by
    by_cases positive : 0 < limit
    · obtain ⟨finalEnv, extra, ran, known, _⟩ := outer_loop limit.toNat 0 limit.toNat limit (by omega) (by omega)
        0 heap initial globals initialN initialState
      exact ⟨finalEnv, extra, ran, by simpa only [PowerDigitSum.maximum, List.range_eq_range'] using known⟩
    · have empty : limit.toNat = 0 := by omega
      refine ⟨initial, [], ?_, ?_⟩
      · simpa only [List.append_nil] using
          (BlockContinues.range_done (module := program) (env := initial) (heap := heap) (globals := globals)
            (name := "a") (next := 0) (stop := limit) (stride := 1) (body := rowBody) (otherwise := [])
            (by simp [Calls.rangeContinues]; omega) .nil)
      · simpa [PowerDigitSum.maximum, PowerDigitSum.scan, empty] using initialState
  obtain ⟨finalEnv, extra, ran, seen, finalBest, finalSeen, _, _⟩ := loopResult
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.extremum_generator_range (maximum := true) (fallback := some (.constant (.int 0)))
    (name := "a") (filters := []) (generators := generators.tail)
    (middle := heap) (afterDefault := heap)
    (.cons (Evaluates.lookup getN) .nil) rfl Evaluates.constant
  have returned := ran.returns (BlockReturns.return_value (rest := []) (Evaluates.lookup finalBest))
  simpa only [initial, generators, extremumFinish, comprehensionTargetsBody, comprehensionTargetBody,
    comprehensionFilters, List.foldr_nil, List.tail_cons] using returned

end data.«project-euler-statements».data.py.project_euler_statements.p56.naive

namespace data.«project-euler-statements».data.py.project_euler_statements.p56.naive
open FormalSW.PyAst

theorem «Returns» (limit : Int) :
    (HeapCalls.scalarFunction P56Ast.module "naive" [.int limit]).Returns := by
  obtain ⟨extra, returned⟩ := result limit []
  exact returned.scalar_returns

theorem «Supported» (limit : Int) :
    (HeapCalls.scalarFunction P56Ast.module "naive" [.int limit]).Supported :=
  («Returns» limit).supported

end data.«project-euler-statements».data.py.project_euler_statements.p56.naive
