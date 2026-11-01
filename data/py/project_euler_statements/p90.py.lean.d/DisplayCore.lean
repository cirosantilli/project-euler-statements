import data.«project-euler-statements».data.py.project_euler_statements.«p90.py.lean.d».RotationCore
import lang.py.FormalSW.BooleanCalls
import lang.py.FormalSW.TruthCalls

/-! The reference display check consumes arbitrary finite requirement lists lazily. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p90.can_show
open FormalSW.PyAst HeapCalls ProjectEulerSolutions DigitDice
set_option Elab.async false

structure Pair where
  x : Nat
  y : Nat
  address : Nat

def Pair.model (pair : Pair) : Nat × Nat := (pair.x, pair.y)
def Pair.reference (pair : Pair) : Mutable.Value := .ref pair.address
def Pair.Valid (pair : Pair) (heap : Mutable.Heap) : Prop :=
  heap[pair.address]? = some (.tuple [number pair.x, number pair.y])

def accepted (a b : List Nat) (pair : Pair) : Bool :=
  (decide (pair.x ∈ a) && decide (pair.y ∈ b)) || (decide (pair.y ∈ a) && decide (pair.x ∈ b))

def expression : Expr := .boolOp .or [
  .boolOp .and [.membership (.name "x") (.name "aa") false, .membership (.name "y") (.name "bb") false],
  .boolOp .and [.membership (.name "y") (.name "aa") false, .membership (.name "x") (.name "bb") false]]

def body : List Stmt :=
  [.assign [.tuple [.name "x", .name "y"]] (.name "$formalsw.unpack")] ++ truthBody true expression

private theorem member_truth (labels : List Nat) (digit address : Nat) (env : HeapCalls.Env)
    (heap : Mutable.Heap) (globals : Mutable.Globals) (item container : String)
    (getItem : env item = some (number digit)) (getContainer : env container = some (.ref address))
    (found : heap[address]? = some (.list (labels.map number))) :
    EvaluatesTruth program env (.membership (.name item) (.name container) false)
      heap (decide (digit ∈ labels)) globals := by
  exact ⟨_, membership_evaluates labels digit address heap env globals _ _ false
    (Evaluates.lookup getItem) (Evaluates.lookup getContainer) found, rfl⟩

theorem condition (a b : List Nat) (addressA addressB : Nat) (pair : Pair)
    (env : HeapCalls.Env) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (foundA : heap[addressA]? = some (.list (a.map number)))
    (foundB : heap[addressB]? = some (.list (b.map number)))
    (getA : env "aa" = some (.ref addressA)) (getB : env "bb" = some (.ref addressB))
    (getX : env "x" = some (number pair.x)) (getY : env "y" = some (number pair.y)) :
    EvaluatesTruth program env expression heap (accepted a b pair) globals :=
  ((member_truth a pair.x addressA env heap globals "x" "aa" getX getA foundA).and
    (member_truth b pair.y addressB env heap globals "y" "bb" getY getB foundB)).or
    ((member_truth a pair.y addressA env heap globals "y" "aa" getY getA foundA).and
      (member_truth b pair.x addressB env heap globals "x" "bb" getX getB foundB))

/-- Unpacking requirements and short-circuiting the generator preserves the entire heap. -/
theorem loop (a b : List Nat) (addressA addressB address : Nat)
    (pairs remaining : List Pair) (position : Nat) (heap : Mutable.Heap)
    (globals : Mutable.Globals) (env : HeapCalls.Env)
    (foundA : heap[addressA]? = some (.list (a.map number)))
    (foundB : heap[addressB]? = some (.list (b.map number)))
    (found : heap[address]? = some (.list (pairs.map Pair.reference)))
    (valid : ∀ pair ∈ remaining, pair.Valid heap)
    (suffix : pairs.drop position = remaining)
    (getA : env "aa" = some (.ref addressA)) (getB : env "bb" = some (.ref addressB)) :
    BlockReturns program env
      [.sequenceStepLoop "$formalsw.unpack" (.ref address) position body [], .return (.constant (.bool true))]
      heap (.scalar (.bool (remaining.all (accepted a b)))) heap globals := by
  have sequence : Mutable.sequence (sequenceValue (.ref address)) heap =
      some (.ok (pairs.map Pair.reference), heap) := by simp [sequenceValue, Mutable.sequence, found]
  induction remaining generalizing position env with
  | nil =>
      apply BlockReturns.sequence_done sequence
      · have missing : pairs[position]? = none := List.getElem?_eq_none_iff.mpr (List.drop_eq_nil_iff.mp suffix)
        simp [missing]
      · exact BlockReturns.return_value Evaluates.constant
  | cons pair rest ih =>
      have item : pairs[position]? = some pair := by
        simpa [suffix] using (List.head?_drop (l := pairs) (i := position)).symm
      have fields := valid pair (by simp)
      change heap[pair.address]? = some (.tuple [number pair.x, number pair.y]) at fields
      let bound := assignNames (setLocal env "$formalsw.unpack" pair.reference) ["x", "y"] [number pair.x, number pair.y]
      have nextA : bound "aa" = some (.ref addressA) := by simpa [bound, assignNames, setLocal] using getA
      have nextB : bound "bb" = some (.ref addressB) := by simpa [bound, assignNames, setLocal] using getB
      obtain ⟨value, tested, truth⟩ := condition a b addressA addressB pair bound heap globals foundA foundB
        nextA nextB (by simp [bound, assignNames, setLocal]) (by simp [bound, assignNames, setLocal])
      apply BlockReturns.sequence_step (value := pair.reference) sequence (by simp [item])
      apply BlockReturns.unpack (names := ["x", "y"]) (items := [number pair.x, number pair.y]) (afterUnpack := heap) rfl
        (Evaluates.lookup rfl)
      · simp [Pair.reference, Mutable.sequence, fields]
      · rfl
      · cases ok : accepted a b pair with
        | false =>
            simp only [List.all_cons, ok, Bool.false_and]
            apply BlockReturns.branch tested (by simpa only [ok] using truth)
            exact BlockReturns.return_value Evaluates.constant
        | true =>
            simp only [List.all_cons, ok, Bool.true_and]
            apply BlockReturns.branch tested (by simpa only [ok] using truth)
            have tail : pairs.drop (position + 1) = rest := by simp [List.drop_add_one_eq_tail_drop, suffix]
            have continued := ih (position + 1) bound (fun p mem => valid p (by simp [mem])) tail nextA nextB
            simpa [body, truthBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using continued

/-- The actual `all` generator returns the conjunction of the list-membership predicates. -/
theorem generator (a b : List Nat) (addressA addressB address : Nat) (pairs : List Pair)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (globals : Mutable.Globals)
    (foundA : heap[addressA]? = some (.list (a.map number)))
    (foundB : heap[addressB]? = some (.list (b.map number)))
    (found : heap[address]? = some (.list (pairs.map Pair.reference)))
    (valid : ∀ pair ∈ pairs, pair.Valid heap)
    (getA : env "aa" = some (.ref addressA)) (getB : env "bb" = some (.ref addressB))
    (getPairs : env "required_pairs" = some (.ref address)) :
    Evaluates program env
      (.consumeGenerator (.builtinCall .all []) expression [(.tuple [.name "x", .name "y"], .name "required_pairs", [])])
      heap (.scalar (.bool (pairs.all (accepted a b)))) heap globals := by
  apply Evaluates.truth_generator_sequence (universal := true)
    (by intros; simp) (by intros; simp) (by intros; simp) (Evaluates.lookup getPairs)
    (items := pairs.map Pair.reference)
  · simp [Mutable.sequence, found]
  · apply loop a b addressA addressB address pairs pairs 0 heap globals _ foundA foundB found valid rfl
    · simpa [comprehensionTargetsEnv, targetLocals] using getA
    · simpa [comprehensionTargetsEnv, targetLocals] using getB

end data.«project-euler-statements».data.py.project_euler_statements.p90.can_show
