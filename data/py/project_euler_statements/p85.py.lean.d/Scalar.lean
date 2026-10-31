import data.«project-euler-statements».data.py.project_euler_statements.«p85.py.lean.d».Execution

/-! The scalar call model selected for the reference's immediately unpacked tuples. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p85.Scalar
open FormalSW.PyAst Calls
open ProjectEulerSolutions.RectangleApproximation ProjectEulerSolutions.RectangleSearch
open ProjectEulerSolutions.TriPentHex (triangular)
set_option Elab.async false

abbrev integer (n : Int) : Constant := .int n
abbrev number (n : Nat) : Constant := .int n

structure Locals (env : ScalarEnv) (target : Int) (m : Nat) (best : Grid) : Prop where
  targetValue : env "target" = some (integer target)
  rowValue : env "m" = some (number m)
  areaValue : env "best_area" = some (number (best.1 * best.2))
  differenceValue : env "best_diff" = some (integer (error target best))

private theorem triangular_evaluate (env : ScalarEnv) (name : String) (n : Nat)
    (found : env name = some (number n)) :
    Evaluates program env (.binOp
      (.binOp (.name name) .mult (.binOp (.name name) .add (.constant (.int 1))))
      .floorDiv (.constant (.int 2))) (number (triangular n)) := by
  apply Evaluates.binary (av := number (n * (n + 1))) (bv := number 2)
  · exact Evaluates.binary (av := number n) (bv := number (n + 1)) (Evaluates.lookup found)
      (Evaluates.binary (Evaluates.lookup found) Evaluates.constant (by simp [scalarBinary, number]))
      (by simp [scalarBinary, number])
  · exact Evaluates.constant
  · simp [scalarBinary, number, triangular, Int.natCast_ediv]

theorem rect_count_result (m n : Nat) :
    ReturnsValue program "rect_count" [number m, number n] (number (count m n)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary (av := number (triangular m)) (bv := number (triangular n))
  · exact triangular_evaluate _ "m" m rfl
  · exact triangular_evaluate _ "n" n rfl
  · simp [scalarBinary, number, count]

theorem count_evaluate (m n : Nat) (column : String) (env : ScalarEnv)
    (getM : env "m" = some (number m)) (getN : env column = some (number n)) :
    Evaluates program env (countExpression column) (number (count m n)) :=
  Evaluates.call (.cons (Evaluates.lookup getM) (.cons (Evaluates.lookup getN) .nil)) (rect_count_result m n)

theorem condition_evaluate (target : Int) (m n : Nat) (best : Grid) (column : String)
    (env : ScalarEnv) (ready : Locals env target m best) (getN : env column = some (number n)) :
    Evaluates program env (condition column)
      (.bool (decide ((count m n : Int) ≤ target + error target best))) := by
  apply Evaluates.compare (count_evaluate m n column env ready.rowValue getN)
    (Evaluates.binary (Evaluates.lookup ready.targetValue) (Evaluates.lookup ready.differenceValue) rfl)
  simp [scalarCompare, evalCmpOp]

theorem difference_evaluate (target : Int) (m n : Nat) (env : ScalarEnv)
    (getM : env "m" = some (number m)) (getN : env "n" = some (number n))
    (getTarget : env "target" = some (integer target)) :
    Evaluates program env differenceExpression (integer (distance target m n)) := by
  apply Evaluates.builtin (values := [integer ((count m n : Int) - target)])
  · exact .cons (Evaluates.binary (count_evaluate m n "n" env getM getN) (Evaluates.lookup getTarget) rfl) .nil
  · simp [Primitive.apply, absoluteValue, integer, distance]

theorem iteration (target : Int) (m n : Nat) (best : Grid) (env : ScalarEnv)
    (ready : Locals env target m best) (getN : env "n" = some (number n))
    (following : List Stmt) (answer : Constant)
    (rest : ∀ nextEnv, Locals nextEnv target m (choose target best (m, n)) →
      nextEnv "n" = some (number (n + 1)) → BlockReturns program nextEnv following answer) :
    BlockReturns program env (innerBody ++ following) answer := by
  let assigned := env.set "diff" (integer (distance target m n))
  have tested : Evaluates program assigned (.compare (.name "diff") [(.lt, .name "best_diff")])
      (.bool (decide (error target (m, n) < error target best))) := by
    apply Evaluates.compare (av := integer (distance target m n)) (bv := integer (error target best))
      (Evaluates.lookup (by simp [assigned, ScalarEnv.set]))
      (Evaluates.lookup (by simpa [assigned, ScalarEnv.set] using ready.differenceValue))
    simp [scalarCompare, evalCmpOp, error]
  apply BlockReturns.assign (difference_evaluate target m n env ready.rowValue getN ready.targetValue)
  by_cases improves : error target (m, n) < error target best
  · let updated := assignNames assigned ["best_area", "best_diff"] [number (m * n), integer (error target (m, n))]
    let advanced := updated.set "n" (number (n + 1))
    apply BlockReturns.branch (value := .bool true) (by simpa only [improves, decide_true] using tested)
    apply BlockReturns.unpack (names := ["best_area", "best_diff"])
      (results := [number (m * n), integer (error target (m, n))]) rfl rfl
    · exact .cons (Evaluates.binary
        (Evaluates.lookup (by simpa [assigned, ScalarEnv.set] using ready.rowValue))
        (Evaluates.lookup (by simpa [assigned, ScalarEnv.set] using getN)) (by simp [scalarBinary, number]))
        (.cons (Evaluates.lookup (by simp [ScalarEnv.set, error])) .nil)
    apply BlockReturns.augAssign (value := number (n + 1))
    · exact Evaluates.binary
        (Evaluates.lookup (by simpa [updated, assigned, assignNames, ScalarEnv.set] using getN))
        Evaluates.constant (by simp [scalarBinary, number])
    apply rest advanced
    · rw [choose, if_pos improves]
      constructor
      · simpa [advanced, updated, assigned, assignNames, ScalarEnv.set] using ready.targetValue
      · simpa [advanced, updated, assigned, assignNames, ScalarEnv.set] using ready.rowValue
      · simp [advanced, updated, assigned, assignNames, ScalarEnv.set]
      · simp [advanced, updated, assigned, assignNames, ScalarEnv.set]
    · simp [advanced, ScalarEnv.set]
  · let advanced := assigned.set "n" (number (n + 1))
    apply BlockReturns.branch (value := .bool false) (by simpa only [improves, decide_false] using tested)
    apply BlockReturns.augAssign (value := number (n + 1))
    · exact Evaluates.binary (Evaluates.lookup (by simpa [assigned, ScalarEnv.set] using getN))
        Evaluates.constant (by simp [scalarBinary, number])
    apply rest advanced
    · rw [choose, if_neg improves]
      rcases ready with ⟨ht, hm, ha, hd⟩
      constructor <;> simp_all [advanced, assigned, ScalarEnv.set]
    · simp [advanced, ScalarEnv.set]

theorem row_result {target : Int} {m n : Nat} {best final : Grid}
    (run : RowRun target m n best final) (env : ScalarEnv)
    (ready : Locals env target m best) (getN : env "n" = some (number n))
    (following : List Stmt) (answer : Constant)
    (rest : ∀ finalEnv, Locals finalEnv target m final → BlockReturns program finalEnv following answer) :
    BlockReturns program env (innerLoop :: following) answer := by
  induction run generalizing env with
  | stop n best finished =>
      have tested := condition_evaluate target m n best "n" env ready getN
      have inactive : ¬(count m n : Int) ≤ target + error target best := by omega
      apply BlockReturns.while_loop (value := .bool false) (by simpa only [inactive, decide_false] using tested)
      exact rest env ready
  | step n best final active tail ih =>
      have tested := condition_evaluate target m n best "n" env ready getN
      apply BlockReturns.while_loop (value := .bool true) (by simpa only [active, decide_true] using tested)
      change BlockReturns program env (innerBody ++ (innerLoop :: following)) answer
      apply iteration target m n best env ready getN
      intro nextEnv nextReady nextN
      exact ih nextEnv nextReady nextN rest

theorem rows_result {target : Int} {m : Nat} {best final : Grid}
    (run : RowsRun target (referenceRow target) m best final) (env : ScalarEnv)
    (ready : Locals env target m best) (following : List Stmt) (answer : Constant)
    (rest : ∀ finalEnv, finalEnv "best_area" = some (number (final.1 * final.2)) →
      BlockReturns program finalEnv following answer) :
    BlockReturns program env (outerLoop :: following) answer := by
  induction run generalizing env with
  | stop m best finished =>
      have tested := condition_evaluate target m m best "m" env ready ready.rowValue
      have inactive : ¬(count m m : Int) ≤ target + error target best := by omega
      apply BlockReturns.while_loop (value := .bool false) (by simpa only [inactive, decide_false] using tested)
      exact rest env ready.areaValue
  | step m best next final active searched tail ih =>
      have tested := condition_evaluate target m m best "m" env ready ready.rowValue
      apply BlockReturns.while_loop (value := .bool true) (by simpa only [active, decide_true] using tested)
      apply BlockReturns.assign (Evaluates.lookup ready.rowValue)
      let started := env.set "n" (number m)
      have startReady : Locals started target m best := by
        rcases ready with ⟨ht, hm, ha, hd⟩
        constructor <;> simp_all [started, ScalarEnv.set]
      apply row_result searched started startReady (by simp [started, ScalarEnv.set])
      intro rowEnv rowReady
      apply BlockReturns.augAssign (value := number (m + 1))
      · exact Evaluates.binary (Evaluates.lookup rowReady.rowValue) Evaluates.constant (by simp [scalarBinary, number])
      apply ih (rowEnv.set "m" (number (m + 1)))
      · rcases rowReady with ⟨ht, hm, ha, hd⟩
        constructor <;> simp_all [ScalarEnv.set]
      · exact rest

theorem naive_result_of_run (target : Int) (final : Grid)
    (run : RowsRun target (referenceRow target) 1 (1, 1) final) :
    ReturnsValue program "naive" [integer target] (number (final.1 * final.2)) := by
  let args := ((findFunctionIn program.body "naive").getD ([], [])).1
  let initial := argumentEnv args [integer target]
  let areaSet := initial.set "best_area" (number 1)
  let differenceSet := areaSet.set "best_diff" (integer |1 - target|)
  let readyEnv := differenceSet.set "m" (number 1)
  have ready : Locals readyEnv target 1 (1, 1) := by
    constructor
    · rfl
    · rfl
    · rfl
    · simp [readyEnv, differenceSet, ScalarEnv.set, error, distance, count, triangular]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.assign (value := number 1) Evaluates.constant
  apply BlockReturns.assign (value := integer |1 - target|)
  · apply Evaluates.builtin (values := [integer (1 - target)])
    · exact .cons (Evaluates.binary Evaluates.constant (Evaluates.lookup rfl) rfl) .nil
    · simp [Primitive.apply, absoluteValue, integer]
  apply BlockReturns.assign (value := number 1) Evaluates.constant
  apply rows_result run readyEnv ready
  intro finalEnv found
  exact BlockReturns.return_value (Evaluates.lookup found)

theorem naive_result (target : Int) : ∃ final, Optimal target final ∧
    ReturnsValue program "naive" [integer target] (number (final.1 * final.2)) := by
  obtain ⟨final, run⟩ := rows_exists target _ (referenceRow_contract target) 1 (by omega) (1, 1)
  exact ⟨final, run.optimal (referenceRow_contract target), naive_result_of_run target final run⟩

end data.«project-euler-statements».data.py.project_euler_statements.p85.Scalar
