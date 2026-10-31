import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p75.py.ast»
import ProjectEulerStatements.P75
import lang.py.FormalSW.SumCalls
import lang.py.FormalSW.LoopCalls

/-! The exhaustive reference's signed arithmetic and short-circuit triangle test. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p75
open FormalSW.PyAst HeapCalls
set_option Elab.async false

abbrev program := P75Ast.module
abbrev integer (n : Int) : Mutable.Value := .scalar (.int n)
abbrev number (n : Nat) : Mutable.Value := integer n
abbrev third : Expr := .binOp (.binOp (.name "p") .sub (.name "a")) .sub (.name "b")
abbrev ordered : Expr := .compare (.name "a") [(.lt, .name "b"), (.lt, third)]
abbrev square (name : String) : Expr := .binOp (.name name) .mult (.name name)
abbrev pythagorean : Expr := .compare (.binOp (square "a") .add (square "b"))
  [(.eq, .binOp third .pow (.constant (.int 2)))]
abbrev test : Expr := .boolOp .and [ordered, pythagorean]

variable {globals : Mutable.Globals}

theorem third_result (p a b : Nat) (heap : Mutable.Heap) (locals : HeapCalls.Env)
    (getP : locals "p" = some (number p)) (getA : locals "a" = some (number a))
    (getB : locals "b" = some (number b)) :
    Evaluates program locals third heap (integer ((p : Int) - a - b)) heap globals :=
  Evaluates.binary
    (Evaluates.binary (Evaluates.lookup getP) (Evaluates.lookup getA) rfl)
    (Evaluates.lookup getB) rfl

theorem ordered_result (a b : Nat) (c : Int) (heap : Mutable.Heap) (locals : HeapCalls.Env)
    (getA : locals "a" = some (number a)) (getB : locals "b" = some (number b))
    (last : Evaluates program locals third heap (integer c) heap globals) :
    Evaluates program locals ordered heap
      (.scalar (.bool (decide ((a : Int) < b ∧ (b : Int) < c)))) heap globals := by
  apply Evaluates.chain (Evaluates.lookup getA)
  by_cases first : a < b
  · apply Evaluates.Compares.next (Evaluates.lookup getB)
      (compared := .scalar (.bool true)) (afterComparison := heap)
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, first]) rfl
    simpa only [show ((a : Int) < b) from by omega, true_and] using
      (Evaluates.Compares.last last (by rfl))
  · have rejected : ¬ ((a : Int) < b ∧ (b : Int) < c) := by omega
    simpa only [rejected, decide_false] using
      (Evaluates.Compares.stop (module := program) (env := locals) (left := number a)
        (next := (.lt, third)) (rest := []) (op := .lt)
        (Evaluates.lookup getB) (answer := .scalar (.bool false))
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, first]) rfl)

theorem tested (p a b : Nat) (heap : Mutable.Heap) (locals : HeapCalls.Env)
    (getP : locals "p" = some (number p)) (getA : locals "a" = some (number a))
    (getB : locals "b" = some (number b)) :
    Evaluates program locals test heap
      (.scalar (.bool (decide
        (ProjectEulerStatements.PythagoreanPerimeterCounting.triangle p a b))))
      heap globals := by
  let c : Int := (p : Int) - a - b
  have last := third_result (globals := globals) p a b heap locals getP getA getB
  have order := ordered_result (globals := globals) a b c heap locals getA getB last
  have leftA : Evaluates program locals (square "a") heap (integer ((a : Int) * a))
      heap globals := Evaluates.binary (Evaluates.lookup getA) (Evaluates.lookup getA) rfl
  have leftB : Evaluates program locals (square "b") heap (integer ((b : Int) * b))
      heap globals := Evaluates.binary (Evaluates.lookup getB) (Evaluates.lookup getB) rfl
  have equal : Evaluates program locals pythagorean heap
      (.scalar (.bool (decide ((a : Int) ^ 2 + (b : Int) ^ 2 = c ^ 2)))) heap globals := by
    apply Evaluates.compare
      (Evaluates.binary leftA leftB rfl)
      (Evaluates.binary last Evaluates.constant (by rfl))
    simp [HeapCalls.compare, scalarCompare, evalCmpOp, pow_two, c]
  suffices evaluated : Evaluates program locals test heap
      (.scalar (.bool (decide ((a : Int) < b ∧ (b : Int) < c ∧
        (a : Int) ^ 2 + (b : Int) ^ 2 = c ^ 2)))) heap globals by
    simpa only [c, ProjectEulerStatements.PythagoreanPerimeterCounting.integer_guard]
      using evaluated
  by_cases accepted : (a : Int) < b ∧ (b : Int) < c
  · have reduced : Evaluates program locals ordered heap (.scalar (.bool true)) heap globals := by
      simpa only [accepted, decide_true] using order
    simpa only [and_assoc, accepted, true_and] using
      (Evaluates.boolean_next reduced rfl rfl (Evaluates.boolean_last equal rfl))
  · have reduced : Evaluates program locals ordered heap (.scalar (.bool false)) heap globals := by
      simpa only [accepted, decide_false] using order
    have rejected : ¬ ((a : Int) < b ∧ (b : Int) < c ∧
        (a : Int) ^ 2 + (b : Int) ^ 2 = c ^ 2) := by tauto
    simpa only [rejected, decide_false] using
      (Evaluates.boolean_stop (op := .and) (rest := [pythagorean]) reduced rfl rfl)

end data.«project-euler-statements».data.py.project_euler_statements.p75
