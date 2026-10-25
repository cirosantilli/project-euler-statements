import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p73.py.ast»
import lang.py.FormalSW.CallDefaults
import ProjectEulerStatements.P73

/-! Endpoint locals and the source's short-circuit fraction predicates. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p73
open FormalSW.PyAst Calls ProjectEulerStatements.FractionIntervalCount
set_option Elab.async false

abbrev program := P73Ast.module
abbrev number (n : Int) : Constant := .int n

structure Captured (p : Bounds) (env : ScalarEnv) : Prop where
  lowerNum : env "lower_num" = some (number p.lowerNum)
  lowerDen : env "lower_den" = some (number p.lowerDen)
  upperNum : env "upper_num" = some (number p.upperNum)
  upperDen : env "upper_den" = some (number p.upperDen)

theorem Captured.set {p : Bounds} {env : ScalarEnv} (captured : Captured p env)
    (name : String) (value : Constant) (ln : name ≠ "lower_num") (ld : name ≠ "lower_den")
    (un : name ≠ "upper_num") (ud : name ≠ "upper_den") : Captured p (env.set name value) where
  lowerNum := by simpa [ScalarEnv.set, Ne.symm ln] using captured.lowerNum
  lowerDen := by simpa [ScalarEnv.set, Ne.symm ld] using captured.lowerDen
  upperNum := by simpa [ScalarEnv.set, Ne.symm un] using captured.upperNum
  upperDen := by simpa [ScalarEnv.set, Ne.symm ud] using captured.upperDen

abbrev gcdCondition : Expr := .compare (.call (.name "gcd") [.name "n", .name "d"])
  [(.eq, .constant (.int 1))]
abbrev lowerCondition : Expr := .compare (.binOp (.name "n") .mult (.name "lower_den"))
  [(.gt, .binOp (.name "lower_num") .mult (.name "d"))]
abbrev upperCondition : Expr := .compare (.binOp (.name "n") .mult (.name "upper_den"))
  [(.lt, .binOp (.name "upper_num") .mult (.name "d"))]
abbrev countCondition : Expr := .boolOp .and [gcdCondition, lowerCondition, upperCondition]

theorem gcd_result (n d : Int) (env : ScalarEnv)
    (getN : env "n" = some (number n)) (getD : env "d" = some (number d)) :
    Evaluates program env gcdCondition (.bool (decide (Int.gcd n d = 1))) := by
  apply Evaluates.compare (av := .int (Int.gcd n d)) (bv := .int 1)
  · apply Evaluates.library_call
      (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getD) .nil)) rfl
    change some (Math.gcdCall [.int n, .int d]) = _
    simpa using congrArg some (Math.gcdCall_pair n d)
  · exact Evaluates.constant
  · simp [scalarCompare, evalCmpOp]

theorem lower_result (p : Bounds) (d n : Int) (env : ScalarEnv) (captured : Captured p env)
    (getD : env "d" = some (number d)) (getN : env "n" = some (number n)) :
    Evaluates program env lowerCondition (.bool (decide (p.lowerNum * d < n * p.lowerDen))) := by
  apply Evaluates.compare (av := number (n * p.lowerDen)) (bv := number (p.lowerNum * d))
    (Evaluates.binary (Evaluates.lookup getN) (Evaluates.lookup captured.lowerDen) rfl)
    (Evaluates.binary (Evaluates.lookup captured.lowerNum) (Evaluates.lookup getD) rfl) rfl

theorem upper_result (p : Bounds) (d n : Int) (env : ScalarEnv) (captured : Captured p env)
    (getD : env "d" = some (number d)) (getN : env "n" = some (number n)) :
    Evaluates program env upperCondition (.bool (decide (n * p.upperDen < p.upperNum * d))) := by
  apply Evaluates.compare (av := number (n * p.upperDen)) (bv := number (p.upperNum * d))
    (Evaluates.binary (Evaluates.lookup getN) (Evaluates.lookup captured.upperDen) rfl)
    (Evaluates.binary (Evaluates.lookup captured.upperNum) (Evaluates.lookup getD) rfl) rfl

/-- The source evaluates no later conjunct after a failed gcd or lower-bound test. -/
theorem condition_result (p : Bounds) (d n : Int) (env : ScalarEnv) (captured : Captured p env)
    (getD : env "d" = some (number d)) (getN : env "n" = some (number n)) :
    Evaluates program env (.boolOp .and [countCondition]) (.bool (decide (accepted p d n))) := by
  have gcdTest := gcd_result n d env getN getD
  have lowerTest := lower_result p d n env captured getD getN
  have upperTest := upper_result p d n env captured getD getN
  apply Evaluates.boolean_last
  by_cases coprime : Int.gcd n d = 1
  · apply Evaluates.boolean_continue (first := .bool true)
      (by simpa only [coprime, decide_true] using gcdTest) rfl
    by_cases above : p.lowerNum * d < n * p.lowerDen
    · apply Evaluates.boolean_continue (first := .bool true)
        (by simpa only [above, decide_true] using lowerTest) rfl
      simpa only [accepted, between, coprime, above, true_and] using
        (Evaluates.boolean_last (op := .and) upperTest)
    · simpa only [accepted, between, above, false_and, and_false, decide_false] using
        (Evaluates.boolean_stop (op := .and) (value := .bool false) (rest := [upperCondition])
          (by simpa only [above, decide_false] using lowerTest) rfl)
  · simpa only [accepted, coprime, false_and, decide_false] using
      (Evaluates.boolean_stop (op := .and) (value := .bool false)
        (rest := [lowerCondition, upperCondition])
        (by simpa only [coprime, decide_false] using gcdTest) rfl)

abbrev helperArgs : List Arg :=
  [⟨"d", some (.name "int"), none⟩, ⟨"lower_num", some (.name "int"), none⟩,
   ⟨"lower_den", some (.name "int"), none⟩, ⟨"upper_num", some (.name "int"), none⟩,
   ⟨"upper_den", some (.name "int"), none⟩]

abbrev naiveArgs : List Arg :=
  [⟨"limit", some (.name "int"), none⟩, ⟨"lower_num", some (.name "int"), some (.int 1)⟩,
   ⟨"lower_den", some (.name "int"), some (.int 3)⟩,
   ⟨"upper_num", some (.name "int"), some (.int 1)⟩,
   ⟨"upper_den", some (.name "int"), some (.int 2)⟩]

abbrev values (first : Int) (p : Bounds) : List Constant :=
  [number first, number p.lowerNum, number p.lowerDen, number p.upperNum, number p.upperDen]

end data.«project-euler-statements».data.py.project_euler_statements.p73
