import data.«project-euler-statements».data.py.project_euler_statements.«p79.checked.source»
import lang.py.FormalSW.DigitCalls
import lang.py.FormalSW.ReprCalls

/-! Validation preserves the accepted prefix and raises the first malformed attempt's error. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

def invalidTest : Expr := .boolOp .or
  [.compare (.builtinCall .len [.name "attempt"]) [(.notEq, .constant (.int 3))],
   .unaryOp .not (.call (.attribute (.name "attempt") "isdigit") [])]

def invalidMessage : Expr :=
  .binOp (.binOp (.constant (.string "")) .add (.constant (.string "Invalid attempt: ")))
    .add (.builtinCall .repr [.name "attempt"])

def invalidException (s : String) : ExceptionObject :=
  { typeName := "ValueError"
    args := [.string ("Invalid attempt: " ++ Strings.reprValue (.string s))] }

def invalidBody : List Stmt :=
  [.raise (some (.call (.name "ValueError") [invalidMessage]))]

def appendAttempt : List Stmt :=
  [.expr (.call (.attribute (.name "checked") "append") [.name "attempt"])]

def validationBody : List Stmt := [.ifThen invalidTest invalidBody []] ++ appendAttempt

def validationLoop (source : SequenceSource) (position : Nat) : Stmt :=
  .sequenceStepLoop "attempt" source position validationBody []

def naiveCode : List Stmt := executableBody
  ((findFunctionIn program.body "naive").getD ([], [])).2

theorem naive_source : naiveCode =
    [.annAssign (.name "checked") (.subscript (.name "list") (.name "str"))
       (some (.list [])),
     .forIn (.name "attempt") (.name "attempts") validationBody [],
     .return checkedExpression] := rfl

theorem valid_guard (env : HeapCalls.Env) (heap : Mutable.Heap) (s : String)
    (getS : env "attempt" = some (text s)) (length : s.length = 3)
    (digits : Strings.isDigit s = true) :
    BlockContinues program env [.ifThen invalidTest invalidBody []] heap env heap := by
  have sized : Evaluates program env (.builtinCall .len [.name "attempt"])
      heap (number 3) heap := by
    apply Evaluates.builtin (.cons (Evaluates.lookup getS) .nil)
    simp [primitive, Mutable.length, length, number, text]
  have compared : Evaluates program env
      (.compare (.builtinCall .len [.name "attempt"]) [(.notEq, .constant (.int 3))])
      heap (.scalar (.bool false)) heap := by
    exact Evaluates.compare sized Evaluates.constant rfl
  have tested : Evaluates program env (.call (.attribute (.name "attempt") "isdigit") [])
      heap (.scalar (.bool true)) heap := by
    simpa only [digits] using Evaluates.is_digit (module := program)
      (Evaluates.lookup (heap := heap) getS)
      (by intro name equal; cases equal; simp [getS])
  have negated : Evaluates program env
      (.unaryOp .not (.call (.attribute (.name "attempt") "isdigit") []))
      heap (.scalar (.bool false)) heap := Evaluates.unary tested rfl
  have condition : Evaluates program env invalidTest heap (.scalar (.bool false)) heap :=
    Evaluates.boolean_next compared rfl rfl (Evaluates.boolean_last negated rfl)
  exact BlockContinues.branch condition rfl .nil

theorem invalid_guard (env : HeapCalls.Env) (heap : Mutable.Heap) (s : String)
    (getS : env "attempt" = some (text s)) (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false) :
    Evaluates program env invalidTest heap (.scalar (.bool true)) heap := by
  have sized : Evaluates program env (.builtinCall .len [.name "attempt"])
      heap (number s.length) heap :=
    Evaluates.builtin (.cons (Evaluates.lookup getS) .nil) rfl
  by_cases length : s.length = 3
  · have digits : Strings.isDigit s = false := invalid.resolve_left (by simpa using length)
    have compared : Evaluates program env
        (.compare (.builtinCall .len [.name "attempt"]) [(.notEq, .constant (.int 3))])
        heap (.scalar (.bool false)) heap := by
      apply Evaluates.compare sized Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, length]
    have tested : Evaluates program env (.call (.attribute (.name "attempt") "isdigit") [])
        heap (.scalar (.bool false)) heap := by
      simpa only [digits] using Evaluates.is_digit (module := program)
        (Evaluates.lookup (heap := heap) getS)
        (by intro name equal; cases equal; simp [getS])
    have negated : Evaluates program env
        (.unaryOp .not (.call (.attribute (.name "attempt") "isdigit") []))
        heap (.scalar (.bool true)) heap := Evaluates.unary tested rfl
    exact Evaluates.boolean_next compared rfl rfl (Evaluates.boolean_last negated rfl)
  · have compared : Evaluates program env
        (.compare (.builtinCall .len [.name "attempt"]) [(.notEq, .constant (.int 3))])
        heap (.scalar (.bool true)) heap := by
      apply Evaluates.compare sized Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp]
      omega
    exact Evaluates.boolean_stop compared rfl rfl

theorem invalid_message (env : HeapCalls.Env) (heap : Mutable.Heap) (s : String)
    (getS : env "attempt" = some (text s)) :
    Evaluates program env invalidMessage heap
      (text ("Invalid attempt: " ++ Strings.reprValue (.string s))) heap := by
  have messageStart : Evaluates program env
      (.binOp (.constant (.string "")) .add (.constant (.string "Invalid attempt: ")))
      heap (text "Invalid attempt: ") heap :=
    Evaluates.binary Evaluates.constant Evaluates.constant rfl
  exact Evaluates.binary messageStart (Evaluates.repr (Evaluates.lookup getS)) rfl

theorem invalid_body (env : HeapCalls.Env) (heap : Mutable.Heap) (s : String)
    (getS : env "attempt" = some (text s)) (following : List Stmt) (anchors : Nat)
    (stack : List HeapCalls.Frame) :
    Finishes (step program anchors) ⟨.block (invalidBody ++ following) env, stack, heap⟩
      (.ok ⟨.error (invalidException s), [], heap, anchors⟩) := by
  change Finishes (step program anchors)
    ⟨.block ((.raise (some (.call (.name "ValueError") [invalidMessage]))) :: following) env,
      stack, heap⟩ (.ok ⟨.error (invalidException s), [], heap, anchors⟩)
  refine Finishes.next (following :=
    argumentsState (.raiseException "ValueError") env [] [invalidMessage] stack heap) ?_ ?_
  · rfl
  apply (Evaluates.arguments_reach
    (.cons (invalid_message env heap s getS) .nil) (.raiseException "ValueError") []
    anchors stack).finishes
  exact Finishes.done (by
    simp [step, result, run, primitive, done, protectGenerator,
      Calls.generatorException, invalidException, text])

theorem accepted_attempt (base : Mutable.Heap) (checked : List String)
    (env : HeapCalls.Env) (s : String)
    (getChecked : env "checked" = some (.ref base.length))
    (getAttempt : env "attempt" = some (text s))
    (length : s.length = 3) (digits : Strings.isDigit s = true) :
    BlockContinues program env validationBody (base ++ [.list (checked.map text)]) env
      (base ++ [.list ((checked ++ [s]).map text)]) := by
  apply (valid_guard env _ s getAttempt length digits).append
  apply BlockContinues.discard
  have appended := Evaluates.append (module := program) (globals := [])
    (value := text s) (current := checked.map text)
    (Evaluates.lookup (name := "checked") getChecked)
    (show (base ++ [.list (checked.map text)])[base.length]? =
      some (.list (checked.map text)) by simp)
    (Evaluates.lookup (name := "attempt") getAttempt) (by simp)
  simpa [List.map_append] using appended

theorem rejected_attempt (env : HeapCalls.Env) (heap : Mutable.Heap) (s : String)
    (getAttempt : env "attempt" = some (text s))
    (invalid : s.length ≠ 3 ∨ Strings.isDigit s = false)
    (following : List Stmt) :
    SourceResult (.block (validationBody ++ following) env) heap
      (.error (invalidException s)) heap := by
  intro anchors stack
  refine Finishes.next (following := ⟨.expr invalidTest env,
    .branch invalidBody [] (appendAttempt ++ following) env :: stack, heap⟩) rfl ?_
  apply (invalid_guard env heap s getAttempt invalid anchors _).finishes
  refine Finishes.next (following :=
    ⟨.block (invalidBody ++ (appendAttempt ++ following)) env, stack, heap⟩) ?_ ?_
  · simp [step, run, Mutable.truth, scalarTruth]
  exact invalid_body env heap s getAttempt _ anchors stack

end data.«project-euler-statements».data.py.project_euler_statements.p79
