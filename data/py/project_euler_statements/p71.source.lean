import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p71.py.ast»
import lang.py.FormalSW.Calls
import ProjectEulerStatements.P71

/-! The exhaustive Python loops implement the finite reduced-fraction reference scan. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p71
open FormalSW.PyAst Calls ProjectEulerStatements.FractionSearch
set_option Elab.async false

abbrev program := P71Ast.module
abbrev number (n : Nat) : Constant := .int n
abbrev flag (b : Bool) : Constant := .bool b

theorem better_frac.result (a b c d : Nat) :
    ReturnsValue program "better_frac" [number a, number b, number c, number d]
      (flag (decide (c * b < a * d))) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.compare (av := number (a * d)) (bv := number (c * b))
    (Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl)
      (by simp [scalarBinary]))
    (Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl)
      (by simp [scalarBinary]))
  simp [scalarCompare, evalCmpOp]
  norm_cast

theorem is_reduced.result (n d : Nat) :
    ReturnsValue program "is_reduced" [number n, number d]
      (flag (decide (Nat.Coprime n d))) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.compare (av := number (Nat.gcd n d)) (bv := number 1)
  · apply Evaluates.library_call
      (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) rfl
    change some (Math.gcdCall [.int n, .int d]) = _
    simpa [number] using congrArg some (Math.gcdCall_pair (n : Int) (d : Int))
  · exact Evaluates.constant
  · simp [scalarCompare, evalCmpOp, Nat.Coprime]

structure Ready (a b : Nat) (best : Pair) (env : ScalarEnv) : Prop where
  num : env "num" = some (number a)
  den : env "den" = some (number b)
  bestN : env "best_n" = some (number best.1)
  bestD : env "best_d" = some (number best.2)

def accepted (a b n d : Nat) (best : Pair) : Prop :=
  Nat.Coprime n d ∧ n * b < a * d ∧ best.1 * d < n * best.2

instance (a b n d : Nat) (best : Pair) : Decidable (accepted a b n d best) :=
  inferInstanceAs (Decidable (Nat.Coprime n d ∧ n * b < a * d ∧ best.1 * d < n * best.2))

abbrev condition : Expr := .boolOp .and
  [.compare (.name "n") [(.lt, .name "d")],
   .call (.name "is_reduced") [.name "n", .name "d"],
   .compare (.binOp (.name "n") .mult (.name "den"))
     [(.lt, .binOp (.name "num") .mult (.name "d"))],
   .call (.name "better_frac") [.name "n", .name "d", .name "best_n", .name "best_d"]]

abbrev innerBody : List Stmt :=
  [.ifThen condition
    [.assign [.tuple [.name "best_n", .name "best_d"]] (.tuple [.name "n", .name "d"])] []]

abbrev outerBody : List Stmt :=
  [.forIn (.name "n") (.call (.name "range") [.name "d"]) innerBody []]

theorem condition_result (a b n d : Nat) (best : Pair) (env : ScalarEnv)
    (ready : Ready a b best env) (getN : env "n" = some (number n))
    (getD : env "d" = some (number d)) (proper : n < d) :
    Evaluates program env condition (flag (decide (accepted a b n d best))) := by
  have first : Evaluates program env (.compare (.name "n") [(.lt, .name "d")]) (flag true) := by
    apply Evaluates.compare (Evaluates.lookup getN) (Evaluates.lookup getD)
    simp [scalarCompare, evalCmpOp, proper]
  have reduced := Evaluates.call
    (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getD) .nil)) (is_reduced.result n d)
  have below : Evaluates program env
      (.compare (.binOp (.name "n") .mult (.name "den"))
        [(.lt, .binOp (.name "num") .mult (.name "d"))])
      (flag (decide (n * b < a * d))) := by
    apply Evaluates.compare (av := number (n * b)) (bv := number (a * d))
      (Evaluates.binary (Evaluates.lookup getN) (Evaluates.lookup ready.den)
        (by simp [scalarBinary]))
      (Evaluates.binary (Evaluates.lookup ready.num) (Evaluates.lookup getD)
        (by simp [scalarBinary]))
    simp [scalarCompare, evalCmpOp]
    norm_cast
  have better := Evaluates.call
    (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getD)
      (.cons (Evaluates.lookup ready.bestN) (.cons (Evaluates.lookup ready.bestD) .nil))))
    (better_frac.result n d best.1 best.2)
  apply Evaluates.boolean_continue first rfl
  by_cases coprime : Nat.gcd n d = 1
  · apply Evaluates.boolean_continue (first := flag true)
      (by simpa [Nat.Coprime, coprime] using reduced) rfl
    by_cases less : n * b < a * d
    · apply Evaluates.boolean_continue (first := flag true)
        (by simpa only [less, decide_true] using below) rfl
      simpa [accepted, Nat.Coprime, coprime, less] using
        (Evaluates.boolean_last (op := .and) better)
    · simpa only [accepted, less, and_false, false_and, decide_false] using
        (Evaluates.boolean_stop (op := .and) (rest :=
          [.call (.name "better_frac") [.name "n", .name "d", .name "best_n", .name "best_d"]])
          (by simpa only [less, decide_false] using below) rfl)
  · simpa [accepted, Nat.Coprime, coprime] using
      (Evaluates.boolean_stop (op := .and) (rest :=
        [.compare (.binOp (.name "n") .mult (.name "den"))
           [(.lt, .binOp (.name "num") .mult (.name "d"))],
         .call (.name "better_frac") [.name "n", .name "d", .name "best_n", .name "best_d"]])
        (by simpa [Nat.Coprime, coprime] using reduced) rfl)

theorem visit_eq (a b n d : Nat) (best : Pair) (positive : 0 < d) (proper : n < d) :
    visit a b best (n, d) = if accepted a b n d best then (n, d) else best := by
  by_cases c : Nat.Coprime n d <;> by_cases below : n * b < a * d <;>
    by_cases better : best.1 * d < n * best.2 <;>
    simp [visit, Valid, choose, accepted, positive, proper, c, below, better]

/-- An inner loop traverses every numerator at its denominator, preserving target locals. -/
theorem inner_result (a b d first count : Nat) (best : Pair) (env : ScalarEnv)
    (positive : 0 < d) (length : first + count = d) (ready : Ready a b best env)
    (getD : env "d" = some (number d)) (tail : List Stmt) (answer : Constant)
    (done : ∀ nextEnv, Ready a b
      ((List.range' first count).foldl (fun p n => visit a b p (n, d)) best) nextEnv →
      BlockReturns program nextEnv tail answer) :
    BlockReturns program env
      (.rangeStepLoop "n" first d 1 innerBody [] :: tail) answer := by
  induction count generalizing first best env with
  | zero =>
      apply BlockReturns.range_done (by simp [rangeContinues]; omega)
      exact done env (by simpa using ready)
  | succ count ih =>
      let entered := env.set "n" (number first)
      have enteredReady : Ready a b best entered := by
        constructor <;> simp [entered, ScalarEnv.set, ready.num, ready.den, ready.bestN,
          ready.bestD]
      have enteredD : entered "d" = some (number d) := by simpa [entered, ScalarEnv.set] using getD
      have tested := condition_result a b first d best entered enteredReady
        (by simp [entered, ScalarEnv.set]) enteredD (by omega)
      apply BlockReturns.range_step (by simp [rangeContinues]; omega)
      by_cases chosen : accepted a b first d best
      · apply BlockReturns.branch (value := flag true)
          (by simpa only [chosen, decide_true] using tested)
        let next := assignNames entered ["best_n", "best_d"] [number first, number d]
        apply BlockReturns.unpack (names := ["best_n", "best_d"])
          (results := [number first, number d])
          rfl rfl (.cons (Evaluates.lookup (by simp [entered, ScalarEnv.set]))
            (.cons (Evaluates.lookup enteredD) .nil))
        have nr : Ready a b (first, d) next := by
          constructor <;> simp [next, assignNames, ScalarEnv.set, enteredReady.num,
            enteredReady.den]
        have nd : next "d" = some (number d) := by
          simpa [next, assignNames, ScalarEnv.set] using enteredD
        have rest := ih (first + 1) (first, d) next (by omega) nr nd
          (fun nextEnv h => done nextEnv (by
            simpa only [List.range'_succ, List.foldl_cons,
              visit_eq a b first d best positive (by omega),
              if_pos chosen] using h))
        simpa only [loopContinuation, show loopControl innerBody = false from rfl,
          Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one] using rest
      · apply BlockReturns.branch (value := flag false)
          (by simpa only [chosen, decide_false] using tested)
        have rest := ih (first + 1) best entered (by omega) enteredReady enteredD
          (fun nextEnv h => done nextEnv (by
            simpa only [List.range'_succ, List.foldl_cons,
              visit_eq a b first d best positive (by omega),
              if_neg chosen] using h))
        simpa only [loopContinuation, show loopControl innerBody = false from rfl,
          Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one] using rest

/-- Denominators descend to zero exactly as in the exhaustive mathematical model. -/
theorem outer_result (a b count : Nat) (best : Pair) (env : ScalarEnv)
    (ready : Ready a b best env) :
    BlockReturns program env
      [.rangeStepLoop "d" count 0 (-1) outerBody [], .return (.name "best_n")]
      (number (exhaustive a b count best).1) := by
  induction count generalizing best env with
  | zero =>
      apply BlockReturns.range_done (by simp [rangeContinues])
      exact BlockReturns.return_value (Evaluates.lookup ready.bestN)
  | succ count ih =>
      apply BlockReturns.range_step (by simp [rangeContinues])
      let entered := env.set "d" (number (count + 1))
      have enteredReady : Ready a b best entered := by
        constructor <;> simp [entered, ScalarEnv.set, ready.num, ready.den, ready.bestN,
          ready.bestD]
      apply BlockReturns.for_range (values := [number (count + 1)])
        (.cons (Evaluates.lookup (by simp [ScalarEnv.set])) .nil) rfl
      apply inner_result a b (count + 1) 0 (count + 1) best entered (by omega) (by omega)
        enteredReady (by simp [entered, ScalarEnv.set])
      intro nextEnv nextReady
      have rest := ih (row a b (count + 1) best) nextEnv (by
        simpa only [row, List.range_eq_range', Nat.zero_add] using nextReady)
      simpa only [loopContinuation, show loopControl outerBody = false from rfl,
        Bool.false_eq_true, if_false, exhaustive, Int.natCast_add, Int.natCast_one,
        Int.add_neg_cancel_right] using rest

theorem left_of.result (limit : Int) (a b : Nat) :
    ReturnsValue program "left_of" [.int limit, number a, number b]
      (number (exhaustive a b limit.toNat (0, 1)).1) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.unpack (names := ["best_n", "best_d"]) (results := [number 0, number 1])
    rfl rfl (.cons Evaluates.constant (.cons Evaluates.constant .nil))
  apply BlockReturns.for_range
    (.cons (Evaluates.lookup rfl) (.cons Evaluates.constant
      (.cons (Evaluates.unary Evaluates.constant rfl) .nil))) rfl
  by_cases nonnegative : 0 ≤ limit
  · have cast : (limit.toNat : Int) = limit := Int.toNat_of_nonneg nonnegative
    rw [← cast]
    exact outer_result a b limit.toNat (0, 1) _ ⟨rfl, rfl, rfl, rfl⟩
  · have empty : limit.toNat = 0 := by omega
    rw [empty, exhaustive]
    apply BlockReturns.range_done (by simp [rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup rfl)

namespace naive

theorem body_result (limit : Int) (a b : Nat) :
    BlockReturns program
      (argumentEnv ((findFunctionIn program.body "naive").getD ([], [])).1
        [.int limit, number a, number b])
      (executableBody ((findFunctionIn program.body "naive").getD ([], [])).2)
      (number (exhaustive a b limit.toNat (0, 1)).1) := by
  apply BlockReturns.return_value
  exact Evaluates.call (.cons (Evaluates.lookup rfl)
    (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil))) (left_of.result limit a b)

theorem result (limit num den : Int) (positive : 0 < num) (proper : num < den) :
    ReturnsValue program "naive" [.int limit, .int num, .int den]
      (number (ProjectEulerStatements.P71.naive limit num den)) := by
  have castN : (num.toNat : Int) = num := Int.toNat_of_nonneg (by omega)
  have castD : (den.toNat : Int) = den := Int.toNat_of_nonneg (by omega)
  change ReturnsValue program "naive" _
    (number (exhaustive num.toNat den.toNat limit.toNat (0, 1)).1)
  apply BlockReturns.function rfl rfl
  simpa only [number, castN, castD] using body_result limit num.toNat den.toNat

theorem one_argument_result (limit : Int) :
    ReturnsValue program "naive" [.int limit]
      (number (ProjectEulerStatements.P71.naive limit)) :=
  BlockReturns.function_defaults rfl (by simp) rfl (body_result limit 3 7)

theorem two_argument_result (limit num : Int) (positive : 0 < num) (proper : num < 7) :
    ReturnsValue program "naive" [.int limit, .int num]
      (number (ProjectEulerStatements.P71.naive limit num)) := by
  have castN : (num.toNat : Int) = num := Int.toNat_of_nonneg (by omega)
  apply BlockReturns.function_defaults rfl (by simp) rfl
  simpa only [number, castN] using body_result limit num.toNat 7

end naive
end data.«project-euler-statements».data.py.project_euler_statements.p71
