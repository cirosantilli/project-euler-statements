import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p90.py.ast»
import lang.py.FormalSW.MembershipCalls
import ProjectEulerSolutions.Lib.DigitDice
import ProjectEulerSolutions.Lib.HeapCollection

/-! The reference expands a private copy, keeping the original list and all its aliases intact. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p90
open FormalSW.PyAst HeapCalls ProjectEulerSolutions DigitDice
set_option Elab.async false

abbrev program := P90Ast.module
abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
abbrev working (base : Mutable.Heap) (labels : List Nat) (garbage : Mutable.Heap) :=
  HeapCollection.working base (labels.map number) garbage

/-- Integer membership in the caller's list agrees with natural-number membership. -/
theorem membership_evaluates (labels : List Nat) (digit address : Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (element container : Expr) (negated : Bool)
    (needle : Evaluates program env element heap (number digit) heap globals)
    (receiver : Evaluates program env container heap (.ref address) heap globals)
    (found : heap[address]? = some (.list (labels.map number))) :
    Evaluates program env (.membership element container negated) heap
      (.scalar (.bool (if negated then !decide (digit ∈ labels) else decide (digit ∈ labels)))) heap globals := by
  apply Evaluates.membership (.cons needle (.cons receiver .nil))
  have integers : heap[address]? = some (.list ((labels.map (fun (n : Nat) => (n : Int))).map
      (fun n => Mutable.Value.scalar (.int n)))) := by
    simpa only [List.map_map, Function.comp_def] using found
  simpa using membership_list_ints heap address digit (labels.map (fun (n : Nat) => (n : Int))) integers negated

namespace expand69

def code : List Stmt :=
  match findFunctionIn program.body "expand69" with
  | some (_, body) => executableBody body
  | none => []

def loopCode : List Stmt :=
  match (code[1]? : Option Stmt) with
  | some (.ifThen _ [.forIn _ _ body _] _) => body
  | _ => []

theorem condition (base : Mutable.Heap) (labels : List Nat) (env : HeapCalls.Env)
    (globals : Mutable.Globals) (getOut : env "out" = some (.ref base.length)) :
    Evaluates program env (.boolOp .or [
      .membership (.constant (.int 6)) (.name "out") false,
      .membership (.constant (.int 9)) (.name "out") false])
      (working base labels []) (.scalar (.bool (decide (6 ∈ labels ∨ 9 ∈ labels)))) (working base labels []) globals := by
  have six := membership_evaluates labels 6 base.length (working base labels []) env globals
    (.constant (.int 6)) (.name "out") false Evaluates.constant (Evaluates.lookup getOut)
    (HeapCollection.found base _ [])
  have nine := membership_evaluates labels 9 base.length (working base labels []) env globals
    (.constant (.int 9)) (.name "out") false Evaluates.constant (Evaluates.lookup getOut)
    (HeapCollection.found base _ [])
  by_cases present : 6 ∈ labels
  · simpa only [present, true_or, decide_true] using
      Evaluates.boolean_stop (op := BoolOp.or)
        (rest := [.membership (.constant (.int 9)) (.name "out") false])
        (by simpa only [present, decide_true] using six) rfl rfl
  · apply Evaluates.boolean_next (flag := false)
      (by simpa only [present, decide_false] using six) rfl rfl
    simpa only [present, false_or] using Evaluates.boolean_last nine rfl

/-- Appending only a missing label preserves all positions already present, including duplicates. -/
theorem add_missing (base : Mutable.Heap) (labels : List Nat) (garbage : Mutable.Heap)
    (digit : Nat) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (getOut : env "out" = some (.ref base.length)) (getDigit : env "d" = some (number digit)) :
    BlockContinues program env loopCode (working base labels garbage) env
      (working base (addLabel labels digit) garbage) globals := by
  have found := HeapCollection.found base (labels.map number) garbage
  have tested := membership_evaluates labels digit base.length (working base labels garbage) env globals
    (.name "d") (.name "out") true (Evaluates.lookup getDigit) (Evaluates.lookup getOut) found
  by_cases present : digit ∈ labels
  · simp only [addLabel, present, ↓reduceIte]
    apply BlockContinues.branch (flag := false) (by simpa only [present, decide_true] using tested) rfl
    exact BlockContinues.nil
  · simp only [addLabel, present, ↓reduceIte]
    apply BlockContinues.branch (flag := true) (by simpa only [present, decide_false] using tested) rfl
    have appended := Evaluates.append (module := program) (globals := globals)
      (Evaluates.lookup getOut) found (Evaluates.lookup getDigit) found
    simpa only [working, List.map_append, List.map_cons, List.map_nil, HeapCollection.store] using
      BlockContinues.discard appended

def afterTwo (env : HeapCalls.Env) : HeapCalls.Env := setLocal (setLocal env "d" (number 6)) "d" (number 9)

/-- Mutating the fresh output list leaves every tuple at its existing address. -/
theorem tuple_preserved (base : Mutable.Heap) (labels replacement : List Nat)
    (garbage : Mutable.Heap) (address : Nat) (items : List Mutable.Value)
    (found : (working base labels garbage)[address]? = some (.tuple items)) :
    (working base replacement garbage)[address]? = some (.tuple items) := by
  have different : base.length ≠ address := by
    intro same
    subst address
    simp only [working, HeapCollection.found] at found
    cases found
  simpa only [List.append_nil] using
    HeapCollection.other_found base (labels.map number) (replacement.map number) garbage []
      address (.tuple items) different found

private theorem sequence (base : Mutable.Heap) (labels : List Nat) (garbage : Mutable.Heap)
    (address : Nat) (found : (working base labels garbage)[address]? = some (.tuple [number 6, number 9])) :
    Mutable.sequence (sequenceValue (.ref address)) (working base labels garbage) =
      some (.ok [number 6, number 9], working base labels garbage) := by
  simp [sequenceValue, Mutable.sequence, found]

/-- The source traverses the rotation labels in order, whether the tuple was pooled or freshly allocated. -/
theorem two_steps (base : Mutable.Heap) (labels : List Nat) (garbage : Mutable.Heap)
    (address : Nat) (found : (working base labels garbage)[address]? = some (.tuple [number 6, number 9]))
    (env : HeapCalls.Env) (globals : Mutable.Globals) (getOut : env "out" = some (.ref base.length)) :
    BlockContinues program env [.sequenceStepLoop "d" (.ref address) 0 loopCode []]
      (working base labels garbage) (afterTwo env)
      (working base (addLabel (addLabel labels 6) 9) garbage) globals := by
  apply BlockContinues.sequence_step (sequence base labels garbage address found) rfl
  apply (add_missing base labels garbage 6 (setLocal env "d" (number 6)) globals
    (by simpa [setLocal] using getOut) rfl).append
  apply BlockContinues.sequence_step
    (sequence base (addLabel labels 6) garbage address (tuple_preserved base labels _ garbage address _ found)) rfl
  apply (add_missing base (addLabel labels 6) garbage 9 (afterTwo env) globals
    (by simpa [afterTwo, setLocal] using getOut) rfl).append
  exact BlockContinues.sequence_done
    (sequence base (addLabel (addLabel labels 6) 9) garbage address (tuple_preserved base labels _ garbage address _ found))
    rfl BlockContinues.nil

end expand69
end data.«project-euler-statements».data.py.project_euler_statements.p90
