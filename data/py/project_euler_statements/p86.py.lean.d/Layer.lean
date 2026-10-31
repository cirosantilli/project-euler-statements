import data.«project-euler-statements».data.py.project_euler_statements.«p86.py.lean.d».Arithmetic
import ProjectEulerSolutions.Lib.NaturalIntervalSum

namespace data.«project-euler-statements».data.py.project_euler_statements.p86
open FormalSW.PyAst Calls ProjectEulerSolutions.CuboidRoute
open scoped BigOperators
set_option Elab.async false

abbrev number (n : Nat) : Constant := .int n
def contribution (c a b : Nat) : Nat := if square ((a + b) ^ 2 + c ^ 2) then 1 else 0
def rowSum (c a first : Nat) : Nat := ∑ b ∈ Finset.Icc first c, contribution c a b
def rowsSum (c first : Nat) : Nat := ∑ a ∈ Finset.Icc first c, rowSum c a a

theorem rowsSum_eq_layer (c : Nat) : rowsSum c 1 = exhaustiveLayer c := by
  simpa only [rowsSum, rowSum, contribution] using (exhaustiveLayer_nested c).symm

abbrev squareExpression : Expr := .call (.name "is_square")
  [.binOp (.binOp (.binOp (.name "a") .add (.name "b")) .pow (.constant (.int 2)))
    .add (.binOp (.name "c") .pow (.constant (.int 2)))]
abbrev innerBody : List Stmt := [.ifThen squareExpression
  [.augAssign (.name "acc") .add (.constant (.int 1))] []]
abbrev outerBody : List Stmt := [.forIn (.name "b")
  (.call (.name "range") [.name "a", .binOp (.name "c") .add (.constant (.int 1))]) innerBody []]

structure Locals (env : ScalarEnv) (c acc : Nat) : Prop where
  side : env "c" = some (number c)
  count : env "acc" = some (number acc)

theorem square_evaluate (c a b : Nat) (env : ScalarEnv)
    (getC : env "c" = some (number c)) (getA : env "a" = some (number a))
    (getB : env "b" = some (number b)) :
    Evaluates program env squareExpression (.bool (decide (square ((a + b) ^ 2 + c ^ 2)))) := by
  apply Evaluates.call (values := [.int ((a + b) ^ 2 + c ^ 2 : Nat)])
  · refine .cons ?_ .nil
    apply Evaluates.binary (av := number ((a + b) ^ 2)) (bv := number (c ^ 2))
    · exact Evaluates.binary (av := number (a + b)) (bv := number 2)
        (Evaluates.binary (Evaluates.lookup getA) (Evaluates.lookup getB) (by simp [scalarBinary, number]))
        Evaluates.constant (by simp [scalarBinary, number])
    · exact Evaluates.binary (Evaluates.lookup getC) Evaluates.constant (by simp [scalarBinary, number])
    · simp [scalarBinary]
  · exact is_square.result _

theorem inner_result (c a b acc : Nat) (env : ScalarEnv) (ready : Locals env c acc)
    (getA : env "a" = some (number a)) (following : List Stmt) (answer : Constant)
    (rest : ∀ finalEnv, Locals finalEnv c (acc + rowSum c a b) → BlockReturns program finalEnv following answer) :
    BlockReturns program env
      (.rangeStepLoop "b" b (c + 1) 1 innerBody [] :: following) answer := by
  by_cases inside : b ≤ c
  · let entered := env.set "b" (number b)
    have enteredC : entered "c" = some (number c) := by simpa [entered, ScalarEnv.set] using ready.side
    have enteredA : entered "a" = some (number a) := by simpa [entered, ScalarEnv.set] using getA
    have enteredAcc : entered "acc" = some (number acc) := by simpa [entered, ScalarEnv.set] using ready.count
    have tested := square_evaluate c a b entered enteredC enteredA (by simp [entered, ScalarEnv.set])
    have sumStep := ProjectEulerSolutions.NaturalIntervalSum.step (contribution c a) b c inside
    change rowSum c a b = contribution c a b + rowSum c a (b + 1) at sumStep
    apply BlockReturns.range_step (by simp [rangeContinues]; omega)
    by_cases accepted : square ((a + b) ^ 2 + c ^ 2)
    · let updated := entered.set "acc" (number (acc + 1))
      have nextReady : Locals updated c (acc + 1) := by
        constructor
        · simpa [updated, ScalarEnv.set] using enteredC
        · simp [updated, ScalarEnv.set]
      have continued := inner_result c a (b + 1) (acc + 1) updated nextReady
        (by simpa [updated, ScalarEnv.set] using enteredA) following answer
        (fun finalEnv finalReady => rest finalEnv (by
          simpa only [sumStep, contribution, if_pos accepted, Nat.add_assoc] using finalReady))
      apply BlockReturns.branch (value := .bool true) (by simpa only [accepted, decide_true] using tested)
      apply BlockReturns.augAssign (value := number (acc + 1))
        (Evaluates.binary (Evaluates.lookup enteredAcc) Evaluates.constant (by simp [scalarBinary, number]))
      exact continued
    · have continued := inner_result c a (b + 1) acc entered ⟨enteredC, enteredAcc⟩ enteredA following answer
        (fun finalEnv finalReady => rest finalEnv (by
          simpa only [sumStep, contribution, if_neg accepted, Nat.zero_add] using finalReady))
      apply BlockReturns.branch (value := .bool false) (by simpa only [accepted, decide_false] using tested)
      exact continued
  · have empty := ProjectEulerSolutions.NaturalIntervalSum.empty (contribution c a) b c (by omega)
    apply BlockReturns.range_done (by simp [rangeContinues]; omega)
    apply rest env
    simpa only [rowSum, empty, Nat.add_zero] using ready
termination_by c + 1 - b
decreasing_by all_goals omega

theorem outer_result (c a acc : Nat) (env : ScalarEnv) (ready : Locals env c acc)
    (following : List Stmt) (answer : Constant)
    (rest : ∀ finalEnv, Locals finalEnv c (acc + rowsSum c a) → BlockReturns program finalEnv following answer) :
    BlockReturns program env
      (.rangeStepLoop "a" a (c + 1) 1 outerBody [] :: following) answer := by
  by_cases inside : a ≤ c
  · let entered := env.set "a" (number a)
    have enteredReady : Locals entered c acc := by
      rcases ready with ⟨hc, ha⟩
      constructor <;> simp_all [entered, ScalarEnv.set]
    have sumStep := ProjectEulerSolutions.NaturalIntervalSum.step (fun i => rowSum c i i) a c inside
    change rowsSum c a = rowSum c a a + rowsSum c (a + 1) at sumStep
    apply BlockReturns.range_step (by simp [rangeContinues]; omega)
    apply BlockReturns.for_range (values := [number a, number (c + 1)])
    · exact .cons (Evaluates.lookup (by simp [ScalarEnv.set]))
        (.cons (Evaluates.binary (Evaluates.lookup enteredReady.side) Evaluates.constant
          (by simp [scalarBinary, number])) .nil)
    · rfl
    apply inner_result c a a acc entered enteredReady (by simp [entered, ScalarEnv.set])
    intro rowEnv rowReady
    exact outer_result c (a + 1) (acc + rowSum c a a) rowEnv rowReady following answer
      (fun finalEnv finalReady => rest finalEnv (by simpa only [sumStep, Nat.add_assoc] using finalReady))
  · have empty := ProjectEulerSolutions.NaturalIntervalSum.empty (fun i => rowSum c i i) a c (by omega)
    apply BlockReturns.range_done (by simp [rangeContinues]; omega)
    apply rest env
    simpa only [rowsSum, empty, Nat.add_zero] using ready
termination_by c + 1 - a
decreasing_by omega

/-- The actual ordered pair loops count the complete layer of cuboids. -/
theorem count_new_cuboids.result (c : Nat) :
    ReturnsValue program "count_new_cuboids" [number c] (number (exhaustiveLayer c)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := number 0) Evaluates.constant
  apply BlockReturns.for_range (values := [number 1, number (c + 1)])
  · exact .cons Evaluates.constant (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant
      (by simp [scalarBinary, number])) .nil)
  · rfl
  apply outer_result c 1 0 _ ⟨rfl, rfl⟩
  intro finalEnv finalReady
  apply BlockReturns.return_value
  exact Evaluates.lookup (by simpa only [Nat.zero_add, rowsSum_eq_layer] using finalReady.count)

end data.«project-euler-statements».data.py.project_euler_statements.p86
