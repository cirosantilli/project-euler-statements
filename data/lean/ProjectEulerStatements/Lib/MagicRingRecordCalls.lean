import ProjectEulerStatements.Lib.MagicRingTextCalls
import Mathlib.Data.String.Basic

/-! Both sources retain the greatest representation of the required width. -/
namespace ProjectEulerStatements.MagicRingRecordCalls
open FormalSW.PyAst HeapCalls MagicRingTextCalls
set_option Elab.async false

def accepted (text : String) (digits : Int) (best : String) : Prop :=
  (text.toList.length : Int) = digits ∧ best < text
instance (text : String) (digits : Int) (best : String) :
    Decidable (accepted text digits best) := by
  unfold accepted
  infer_instance

def record (text : String) (digits : Int) (best : String) : String :=
  if accepted text digits best then text else best

theorem record_max (text : String) (digits : Int) (best : String) :
    record text digits best =
      if (text.toList.length : Int) = digits then max best text else best := by
  unfold record accepted
  by_cases width : (text.toList.length : Int) = digits
  · simp only [width, true_and, if_true]
    by_cases better : best < text
    · rw [if_pos better, max_eq_right (le_of_lt better)]
    · rw [if_neg better, max_eq_left (le_of_not_gt better)]
  · simp only [width, false_and, if_false]

def widthCondition : Expr :=
  .compare (.builtinCall .len [.name "text"]) [(.eq, .name "digits")]
def betterCondition : Expr := .compare (.name "text") [(.gt, .name "best")]
def condition : Expr := .boolOp .and [widthCondition, betterCondition]
def code : List Stmt := [.ifThen condition [.assign [.name "best"] (.name "text")] []]

theorem condition_result (program : Module) (text best : String) (digits : Int)
    (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getText : env "text" = some (string text))
    (getBest : env "best" = some (string best))
    (getDigits : env "digits" = some (.scalar (.int digits))) :
    Evaluates program env condition heap
      (.scalar (.bool (decide (accepted text digits best)))) heap := by
  have width : Evaluates program env widthCondition heap
      (.scalar (.bool (decide ((text.toList.length : Int) = digits)))) heap := by
    apply Evaluates.compare (middle := heap) (afterRight := heap)
      (av := number text.toList.length) (bv := .scalar (.int digits))
    · exact Evaluates.builtin (.cons (Evaluates.lookup getText) .nil)
        (by simp [HeapCalls.primitive, Mutable.length, number])
    · exact Evaluates.lookup getDigits
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  have better : Evaluates program env betterCondition heap
      (.scalar (.bool (decide (best < text)))) heap :=
    Evaluates.compare (middle := heap) (afterRight := heap)
      (Evaluates.lookup getText) (Evaluates.lookup getBest)
      (by simp [HeapCalls.compare, scalarCompare, String.lt_iff])
  by_cases matching : (text.toList.length : Int) = digits
  · change Evaluates program env (.boolOp .and [widthCondition, betterCondition]) heap _ heap
    apply Evaluates.boolean_next (flag := true) (by simpa only [matching, decide_true] using width)
      rfl rfl
    simpa only [accepted, matching, true_and] using Evaluates.boolean_last better rfl
  · simpa only [accepted, matching, false_and, decide_false] using
      (Evaluates.boolean_stop (op := .and) (rest := [betterCondition])
        (by simpa only [matching, decide_false] using width) rfl rfl)

theorem result (program : Module) (text best : String) (digits : Int)
    (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getText : env "text" = some (string text))
    (getBest : env "best" = some (string best))
    (getDigits : env "digits" = some (.scalar (.int digits))) :
    ∃ finalEnv, BlockContinues program env code heap finalEnv heap ∧
      finalEnv "best" = some (string (record text digits best)) ∧
      ∀ name, name ≠ "best" → finalEnv name = env name := by
  have tested := condition_result program text best digits heap env getText getBest getDigits
  by_cases improve : accepted text digits best
  · refine ⟨setLocal env "best" (string text), ?_, ?_, ?_⟩
    · exact BlockContinues.branch (flag := true)
        (by simpa only [improve, decide_true] using tested) rfl
        (BlockContinues.assign (Evaluates.lookup getText))
    · simp [record, improve, setLocal]
    · intro name different; simp [setLocal, different]
  · refine ⟨env, ?_, ?_, ?_⟩
    · exact BlockContinues.branch (flag := false)
        (by simpa only [improve, decide_false] using tested) rfl .nil
    · simpa only [record, if_neg improve] using getBest
    · intros; rfl

end ProjectEulerStatements.MagicRingRecordCalls
