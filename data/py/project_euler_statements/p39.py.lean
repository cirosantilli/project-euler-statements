import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p39.py.ast»
import lang.py.FormalSW.Calls
import ProjectEulerStatements.P39
import ProjectEulerStatements.Lib.ArgMaximum
import Mathlib.Tactic.NormNum

namespace data.«project-euler-statements».data.py.project_euler_statements.p39
open FormalSW.PyAst FormalSW.PyAst.Calls
open ProjectEulerStatements.P39
private abbrev program := P39Ast.module

private def valid (p a b : Nat) : Prop :=
  a < b ∧ b < p - a - b ∧ a ^ 2 + b ^ 2 = (p - a - b) ^ 2
private instance (p a b : Nat) : Decidable (valid p a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private def increment (p a acc b : Nat) : Nat := if valid p a b then acc + 1 else acc
private def row (p a count start acc : Nat) : Nat :=
  (List.range' start count).foldl (increment p a) acc
private def rows (p count start acc : Nat) : Nat :=
  (List.range' start count).foldl (fun acc a => row p a (p + 1) 0 acc) acc

private theorem valid_cast (p a b : Nat) :
    ((a : Int) < b ∧ (b : Int) < (p : Int) - a - b ∧
      (a : Int) * a + b * b = ((p : Int) - a - b) * ((p : Int) - a - b)) ↔ valid p a b := by
  constructor
  · rintro ⟨ab, bc, squares⟩
    have bound : a + b ≤ p := by omega
    have cast : ((p - a - b : Nat) : Int) = (p : Int) - a - b := by omega
    refine ⟨by omega, by omega, ?_⟩
    have eq : ((a ^ 2 + b ^ 2 : Nat) : Int) = ((p - a - b : Nat) : Int) ^ 2 := by
      simpa [cast, pow_two] using squares
    exact_mod_cast eq
  · rintro ⟨ab, bc, squares⟩
    have cast : ((p - a - b : Nat) : Int) = (p : Int) - a - b := by omega
    refine ⟨by omega, by omega, ?_⟩
    have eq := congrArg (fun n : Nat => (n : Int)) squares
    simpa [cast, pow_two] using eq

private abbrev ordered : Expr :=
  .compare (.name "a") [(.lt, .name "b"), (.lt, .name "cc")]
private abbrev square (name : String) : Expr := .binOp (.name name) .mult (.name name)
private abbrev pythagorean : Expr :=
  .compare (.binOp (square "a") .add (square "b")) [(.eq, square "cc")]
private abbrev condition : Expr := .boolOp .and [ordered, pythagorean]
private abbrev innerBody : List Stmt :=
  [.assign [.name "cc"] (.binOp (.binOp (.name "p") .sub (.name "a")) .sub (.name "b")),
   .ifThen condition [.augAssign (.name "c") .add (.constant (.int 1))] []]
private abbrev outerBody : List Stmt :=
  [.forIn (.name "b") (.call (.name "range")
    [.binOp (.name "p") .add (.constant (.int 1))]) innerBody []]

private theorem ordered_result (env : ScalarEnv) (a b c : Int)
    (ha : env "a" = some (.int a)) (hb : env "b" = some (.int b))
    (hc : env "cc" = some (.int c)) :
    Evaluates program env ordered (.bool (decide (a < b ∧ b < c))) := by
  intro stack
  refine .next rfl ((Evaluates.lookup ha _).trans (.next rfl
    ((Evaluates.lookup hb _).trans ?_)))
  by_cases ab : a < b
  · refine .next (by simp [step, scalarCompare, evalCmpOp, ab])
      ((Evaluates.lookup hc (.chainRight .lt (.int b) [] env :: stack)).trans ?_)
    by_cases bc : b < c <;>
      exact .next (by simp [step, scalarCompare, evalCmpOp, ab, bc]) .refl
  · exact .next (by simp [step, scalarCompare, evalCmpOp, ab]) .refl

private theorem square_result (env : ScalarEnv) (name : String) (value : Int)
    (found : env name = some (.int value)) :
    Evaluates program env (square name) (.int (value * value)) :=
  Evaluates.binary (Evaluates.lookup found) (Evaluates.lookup found) rfl

private theorem condition_result (env : ScalarEnv) (p a b : Nat)
    (ha : env "a" = some (.int a)) (hb : env "b" = some (.int b))
    (hc : env "cc" = some (.int ((p : Int) - a - b))) :
    Evaluates program env condition (.bool (decide (valid p a b))) := by
  have squares : Evaluates program env pythagorean
      (.bool (decide ((a : Int) * a + b * b = ((p : Int) - a - b) * ((p : Int) - a - b)))) := by
    exact Evaluates.compare
      (Evaluates.binary (square_result env "a" a ha) (square_result env "b" b hb) rfl)
      (square_result env "cc" ((p : Int) - a - b) hc) rfl
  suffices evaluated : Evaluates program env condition (.bool (decide
      ((a : Int) < b ∧ (b : Int) < (p : Int) - a - b ∧
        (a : Int) * a + b * b = ((p : Int) - a - b) * ((p : Int) - a - b)))) by
    simpa only [valid_cast] using evaluated
  by_cases order : (a : Int) < b ∧ (b : Int) < (p : Int) - a - b
  · apply Evaluates.boolean_continue (first := .bool true)
    · simpa only [decide_eq_true order] using ordered_result env a b ((p : Int) - a - b) ha hb hc
    · rfl
    · apply Evaluates.boolean_last
      simpa [order.1, order.2] using squares
  · have invalid : ¬ ((a : Int) < b ∧ (b : Int) < (p : Int) - a - b ∧
        (a : Int) * a + b * b = ((p : Int) - a - b) * ((p : Int) - a - b)) :=
        fun h => order ⟨h.1, h.2.1⟩
    simp only [decide_eq_false invalid]
    apply Evaluates.boolean_stop
    · simpa only [decide_eq_false order] using ordered_result env a b ((p : Int) - a - b) ha hb hc
    · rfl

private theorem inner_result (p a b acc : Nat) (env : ScalarEnv) (tail : List Stmt)
    (answer : Constant)
    (hp : env "p" = some (.int p)) (ha : env "a" = some (.int a))
    (hb : env "b" = some (.int b)) (hc : env "c" = some (.int acc))
    (rest : ∀ next : ScalarEnv, next "p" = some (.int p) → next "a" = some (.int a) →
      next "c" = some (.int (increment p a acc b)) → BlockReturns program next tail answer) :
    BlockReturns program env (innerBody ++ tail) answer := by
  apply BlockReturns.assign (value := .int ((p : Int) - a - b))
  · exact Evaluates.binary (Evaluates.binary (Evaluates.lookup hp) (Evaluates.lookup ha) rfl)
      (Evaluates.lookup hb) rfl
  · have guard := condition_result (env.set "cc" (.int ((p : Int) - a - b))) p a b
      (by simp [ScalarEnv.set, ha]) (by simp [ScalarEnv.set, hb]) (by simp [ScalarEnv.set])
    by_cases good : valid p a b
    · apply BlockReturns.branch (value := .bool true) (by simpa [good] using guard)
      apply BlockReturns.augAssign (value := .int (acc + 1))
      · exact Evaluates.binary (av := .int acc) (Evaluates.lookup (by simp [ScalarEnv.set, hc])) Evaluates.constant
          (by simp [scalarBinary])
      · apply rest <;> simp [ScalarEnv.set, hp, ha, increment, good]
    · apply BlockReturns.branch (value := .bool false) (by simpa [good] using guard)
      apply rest <;> simp [ScalarEnv.set, hp, ha, hc, increment, good]

private theorem row_result (p a count start acc : Nat) (bound : start + count = p + 1)
    (env : ScalarEnv) (tail : List Stmt) (answer : Constant)
    (hp : env "p" = some (.int p)) (ha : env "a" = some (.int a))
    (hc : env "c" = some (.int acc))
    (rest : ∀ next : ScalarEnv, next "p" = some (.int p) → next "a" = some (.int a) →
      next "c" = some (.int (row p a count start acc)) → BlockReturns program next tail answer) :
    BlockReturns program env (.rangeStepLoop "b" start (p + 1) 1 innerBody [] :: tail) answer := by
  induction count generalizing start acc env with
  | zero =>
      apply BlockReturns.range_done (by simp [rangeContinues]; omega)
      apply rest
      · exact hp
      · exact ha
      · simpa [row] using hc
  | succ count ih =>
      apply BlockReturns.range_step (by simp [rangeContinues]; omega)
      apply inner_result p a start acc
      · simp [ScalarEnv.set, hp]
      · simp [ScalarEnv.set, ha]
      · simp [ScalarEnv.set]
      · simp [ScalarEnv.set, hc]
      · intro next nextP nextA nextC
        have run := ih (start + 1) (increment p a acc start) (by omega) next nextP nextA nextC
          (by simpa [row, List.range'_succ] using rest)
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, innerBody,
          Nat.cast_add, Nat.cast_one] using run

private theorem rows_result (p count start acc : Nat) (bound : start + count = p + 1)
    (env : ScalarEnv) (tail : List Stmt) (answer : Constant)
    (hp : env "p" = some (.int p)) (hc : env "c" = some (.int acc))
    (rest : ∀ next : ScalarEnv, next "p" = some (.int p) →
      next "c" = some (.int (rows p count start acc)) → BlockReturns program next tail answer) :
    BlockReturns program env (.rangeStepLoop "a" start (p + 1) 1 outerBody [] :: tail) answer := by
  induction count generalizing start acc env with
  | zero =>
      apply BlockReturns.range_done (by simp [rangeContinues]; omega)
      apply rest
      · exact hp
      · simpa [rows] using hc
  | succ count ih =>
      apply BlockReturns.range_step (by simp [rangeContinues]; omega)
      apply BlockReturns.for_range (values := [.int (p + 1)])
        (.cons (Evaluates.binary (av := .int p) (Evaluates.lookup (by simp [ScalarEnv.set, hp])) Evaluates.constant
          (by simp [scalarBinary])) .nil) rfl
      apply row_result p start (p + 1) 0 acc (by omega)
      · simp [ScalarEnv.set, hp]
      · simp [ScalarEnv.set]
      · simp [ScalarEnv.set, hc]
      · intro next nextP _ nextC
        have run := ih (start + 1) (row p start (p + 1) 0 acc) (by omega) next nextP nextC
          (by simpa [rows, List.range'_succ] using rest)
        simpa only [Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          innerBody, outerBody, Nat.cast_add, Nat.cast_one] using run

theorem count_solutions.result (p : Nat) :
    ReturnsValue program "count_solutions" [.int p] (.int (countSolutions p)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign Evaluates.constant
  apply BlockReturns.for_range (values := [.int (p + 1)])
    (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant
      (by simp [scalarBinary])) .nil) rfl
  apply rows_result p (p + 1) 0 0 (by omega) _ _ _ rfl rfl
  intro next _ nextC
  apply BlockReturns.return_value
  apply Evaluates.lookup
  simpa [rows, row, increment, valid, countSolutions, List.range_eq_range'] using nextC


private theorem scan_result (count start winner : Nat) :
    ExtremumReturns program ⟨true, "count_solutions", start + count, 1⟩ start
      (some (winner, .int (countSolutions winner)))
      (((List.range' start count).foldl (ProjectEulerStatements.ArgMaximum.select countSolutions) winner : Nat) : Int) := by
  induction count generalizing start winner with
  | zero =>
      simpa using ExtremumReturns.done (module := program)
        (range := ⟨true, "count_solutions", start, 1⟩) (next := start)
        (winner := winner) (score := .int (countSolutions winner)) (by simp [rangeContinues])
  | succ count ih =>
      let chosen := ProjectEulerStatements.ArgMaximum.select countSolutions winner start
      simp only [List.range'_succ, List.foldl_cons]
      apply ExtremumReturns.next (score := .int (countSolutions start))
        (updated := (chosen, .int (countSolutions chosen)))
      · simp [rangeContinues]
      · exact count_solutions.result start
      · by_cases better : countSolutions winner < countSolutions start
        all_goals simp [RangeExtremum.choose, scalarCompare, evalCmpOp, chosen,
          ProjectEulerStatements.ArgMaximum.select, better]
      · simpa [Int.natCast_add, Int.add_assoc, Int.add_comm, Int.add_left_comm] using
          ih (start + 1) chosen

theorem naive.negative (limit : Int) (small : limit < 0) :
    ReturnsValue program "naive" [.int limit] (.int 0) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (c := .bool false)
    (Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarCompare, evalCmpOp]; omega))
  exact Evaluates.constant

/-- The key-based maximum retains perimeter zero when every count is zero. -/
theorem naive.result (limit : Nat) :
    ReturnsValue program "naive" [.int limit] (.int (ProjectEulerStatements.P39.naive limit)) := by
  have expected : ProjectEulerStatements.P39.naive limit =
      (List.range' 1 limit).foldl (ProjectEulerStatements.ArgMaximum.select countSolutions) 0 := by
    simp [ProjectEulerStatements.P39.naive, maxPerimeter,
      ProjectEulerStatements.ArgMaximum.argmax_range_succ]
  rw [expected]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (c := .bool true)
  · exact Evaluates.compare (Evaluates.lookup rfl) Evaluates.constant
      (by simp [scalarCompare, evalCmpOp])
  · apply Evaluates.extremum_range (values := [.int (limit + 1)])
    · exact .cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant
        (by simp [scalarBinary])) .nil
    · rfl
    · apply ExtremumReturns.next (score := .int (countSolutions 0))
        (updated := (0, .int (countSolutions 0)))
      · simp [rangeContinues]
      · exact count_solutions.result 0
      · rfl
      · simpa [Int.add_comm] using scan_result limit 1 0

theorem naive.«Returns» (limit : Int) : (Calls.function program "naive" [.int limit]).Returns := by
  by_cases nonnegative : 0 ≤ limit
  · lift limit to Nat using nonnegative
    exact (naive.result limit).returns
  · exact (naive.negative limit (by omega)).returns

theorem naive.«Supported» (limit : Int) : (Calls.function program "naive" [.int limit]).Supported :=
  (naive.«Returns» limit).supported

end data.«project-euler-statements».data.py.project_euler_statements.p39
