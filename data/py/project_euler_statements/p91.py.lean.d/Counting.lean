import data.«project-euler-statements».data.py.project_euler_statements.«p91.py.lean.d».Predicate
import ProjectEulerSolutions.Lib.LatticeReference
import ProjectEulerSolutions.Lib.NaturalIntervalSum

namespace data.«project-euler-statements».data.py.project_euler_statements.p91.naive
open FormalSW.PyAst Calls ProjectEulerSolutions ProjectEulerSolutions.LatticeRightTriangles
set_option Elab.async false
open scoped BigOperators

abbrev number (n : Nat) : Constant := .int n
def code : List Stmt := executableBody ((findFunctionIn program.body "naive").getD ([], [])).2
def xBody : List Stmt := match (code[1]? : Option Stmt) with | some (.forIn _ _ body _) => body | _ => []
def yBody : List Stmt := match (xBody[0]? : Option Stmt) with | some (.forIn _ _ body _) => body | _ => []
def x2Body : List Stmt := match (yBody[0]? : Option Stmt) with | some (.forIn _ _ body _) => body | _ => []
def innerBody : List Stmt := match (x2Body[0]? : Option Stmt) with | some (.forIn _ _ body _) => body | _ => []
def guardExpression : Expr := match (innerBody[0]? : Option Stmt) with | some (.ifThen test _ _) => test | _ => .constant (.bool false)

def invalid (a b c d : Nat) : Prop := (a = 0 ∧ b = 0) ∨ (c = 0 ∧ d = 0) ∨ (a = c ∧ b = d)
instance (a b c d : Nat) : Decidable (invalid a b c d) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))
def weight (a b c d : Nat) : Nat := rightWeight ((a : Int), (b : Int)) ((c : Int), (d : Int))
def rowSum (n a b c first : Nat) : Nat := ∑ d ∈ Finset.Icc first n, weight a b c d

theorem weight_eq (a b c d : Nat) :
    weight a b c d = if invalid a b c d then 0 else if isRight a b c d then 1 else 0 := by
  have same := (reference_step a b c d 0).symm
  by_cases first : a = 0 ∧ b = 0 <;> by_cases second : c = 0 ∧ d = 0 <;>
    by_cases equal : a = c ∧ b = d <;>
    simpa only [weight, invalid, first, second, equal, ↓reduceIte, natural_isRight,
      Nat.zero_add, true_or, false_or, or_true, or_false] using same

structure RowReady (env : ScalarEnv) (n a b c total : Nat) : Prop where
  bound : env "n" = some (number n)
  firstX : env "x1" = some (number a)
  firstY : env "y1" = some (number b)
  secondX : env "x2" = some (number c)
  count : env "acc" = some (number total)

private theorem and_two (env : ScalarEnv) (left right : Expr) (p q : Bool)
    (first : Evaluates program env left (.bool p)) (second : Evaluates program env right (.bool q)) :
    Evaluates program env (.boolOp .and [left, right]) (.bool (p && q)) := by
  cases p
  · exact Evaluates.boolean_stop first rfl
  · exact Evaluates.boolean_continue first rfl (Evaluates.boolean_last second)

private theorem or_three (env : ScalarEnv) (a b c : Expr) (p q r : Bool)
    (first : Evaluates program env a (.bool p)) (second : Evaluates program env b (.bool q))
    (third : Evaluates program env c (.bool r)) :
    Evaluates program env (.boolOp .or [a, b, c]) (.bool (p || q || r)) := by
  cases p
  · apply Evaluates.boolean_continue first rfl
    cases q
    · exact Evaluates.boolean_continue second rfl (Evaluates.boolean_last third)
    · exact Evaluates.boolean_stop second rfl
  · exact Evaluates.boolean_stop first rfl

theorem guard_result (n a b c d total : Nat) (env : ScalarEnv) (ready : RowReady env n a b c total)
    (getD : env "y2" = some (number d)) :
    Evaluates program env guardExpression (.bool (decide (invalid a b c d))) := by
  simp only [invalid, Bool.decide_or, Bool.decide_and, ← Bool.or_assoc]
  apply or_three
  · apply and_two
    · exact Evaluates.compare (Evaluates.lookup ready.firstX) Evaluates.constant (by simp [scalarCompare, evalCmpOp])
    · exact Evaluates.compare (Evaluates.lookup ready.firstY) Evaluates.constant (by simp [scalarCompare, evalCmpOp])
  · apply and_two
    · exact Evaluates.compare (Evaluates.lookup ready.secondX) Evaluates.constant (by simp [scalarCompare, evalCmpOp])
    · exact Evaluates.compare (Evaluates.lookup getD) Evaluates.constant (by simp [scalarCompare, evalCmpOp])
  · apply and_two
    · exact Evaluates.compare (Evaluates.lookup ready.firstX) (Evaluates.lookup ready.secondX) (by simp [scalarCompare, evalCmpOp])
    · exact Evaluates.compare (Evaluates.lookup ready.firstY) (Evaluates.lookup getD) (by simp [scalarCompare, evalCmpOp])

theorem checked (n a b c d total : Nat) (env : ScalarEnv) (ready : RowReady env n a b c total)
    (getD : env "y2" = some (number d)) :
    Evaluates program env (.call (.name "is_right") [.name "x1", .name "y1", .name "x2", .name "y2"])
      (.bool (isRight a b c d)) :=
  Evaluates.call (.cons (Evaluates.lookup ready.firstX) (.cons (Evaluates.lookup ready.firstY)
    (.cons (Evaluates.lookup ready.secondX) (.cons (Evaluates.lookup getD) .nil))))
    (is_right.result a b c d)

/-- The innermost source loop skips degenerate pairs and increments exactly on a right triangle. -/
theorem row_result (n a b c d total : Nat) (env : ScalarEnv) (ready : RowReady env n a b c total)
    (following : List Stmt) (answer : Constant)
    (rest : ∀ after, RowReady after n a b c (total + rowSum n a b c d) →
      BlockReturns program after following answer) :
    BlockReturns program env (.rangeStepLoop "y2" d (n + 1) 1 innerBody [] :: following) answer := by
  by_cases inside : d ≤ n
  · let entered := env.set "y2" (number d)
    have enteredReady : RowReady entered n a b c total := by
      rcases ready with ⟨hn, ha, hb, hc, ht⟩
      constructor <;> simpa [entered, ScalarEnv.set] using ‹_›
    have getD : entered "y2" = some (number d) := by simp [entered, ScalarEnv.set]
    have step := NaturalIntervalSum.step (weight a b c) d n inside
    change rowSum n a b c d = weight a b c d + rowSum n a b c (d + 1) at step
    apply BlockReturns.range_step (by simp [rangeContinues]; omega)
    by_cases rejected : invalid a b c d
    · apply BlockReturns.branch (value := .bool true)
        (by simpa only [rejected, decide_true] using guard_result n a b c d total entered enteredReady getD)
      apply BlockReturns.continue_loop rfl
      have continued := row_result n a b c (d + 1) total entered enteredReady following answer
        (fun after afterReady => rest after (by
          simpa only [step, weight_eq, if_pos rejected, Nat.zero_add] using afterReady))
      simpa only [Int.natCast_add, Int.natCast_one] using continued
    · apply BlockReturns.branch (value := .bool false)
        (by simpa only [rejected, decide_false] using guard_result n a b c d total entered enteredReady getD)
      by_cases right : isRight a b c d = true
      · apply BlockReturns.branch (value := .bool true)
          (by simpa only [right] using checked n a b c d total entered enteredReady getD)
        apply BlockReturns.augAssign (value := number (total + 1))
          (Evaluates.binary (Evaluates.lookup enteredReady.count) Evaluates.constant (by simp [scalarBinary, number]))
        apply BlockReturns.loop_resume
        let updated := entered.set "acc" (number (total + 1))
        have updatedReady : RowReady updated n a b c (total + 1) := by
          constructor
          · simpa [updated, ScalarEnv.set] using enteredReady.bound
          · simpa [updated, ScalarEnv.set] using enteredReady.firstX
          · simpa [updated, ScalarEnv.set] using enteredReady.firstY
          · simpa [updated, ScalarEnv.set] using enteredReady.secondX
          · rfl
        have continued := row_result n a b c (d + 1) (total + 1) updated updatedReady following answer
          (fun after afterReady => rest after (by
            simpa only [step, weight_eq, if_neg rejected, right, ↓reduceIte, Nat.add_assoc] using afterReady))
        simpa only [Int.natCast_add, Int.natCast_one] using continued
      · have rejectedAngle : isRight a b c d = false := Bool.eq_false_iff.mpr right
        apply BlockReturns.branch (value := .bool false)
          (by simpa only [rejectedAngle] using checked n a b c d total entered enteredReady getD)
        apply BlockReturns.loop_resume
        have continued := row_result n a b c (d + 1) total entered enteredReady following answer
          (fun after afterReady => rest after (by
            simpa only [step, weight_eq, if_neg rejected, if_neg right, Nat.zero_add] using afterReady))
        simpa only [Int.natCast_add, Int.natCast_one] using continued
  · apply BlockReturns.range_done (by simp [rangeContinues]; omega)
    apply rest env
    have empty := NaturalIntervalSum.empty (weight a b c) d n (by omega)
    simpa only [rowSum, empty, Nat.add_zero] using ready
termination_by n + 1 - d
decreasing_by all_goals omega

end data.«project-euler-statements».data.py.project_euler_statements.p91.naive
