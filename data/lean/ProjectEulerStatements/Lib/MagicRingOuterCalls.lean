import ProjectEulerStatements.Lib.MagicRingTextCalls
import lang.py.FormalSW.LoopCalls
import Mathlib.Data.List.TakeWhile

/-! Forced outer labels are appended until the first invalid label or the end of the ring. -/
namespace ProjectEulerStatements.MagicRingOuterCalls
open FormalSW.PyAst HeapCalls MagicRingTextCalls
set_option Elab.async false

abbrev integer (value : Int) : Mutable.Value := .scalar (.int value)
def encodeInts (values : List Int) : List Mutable.Value := values.map integer
def working (base : Mutable.Heap) (values : List Int) : Mutable.Heap :=
  base ++ [.list (encodeInts values)]
def forcedValue (n : Nat) (inner : List Nat) (target : Int) (index : Nat) : Int :=
  target - ((inner[index]?).getD 0 : Int) - ((inner[(index + 1) % n]?).getD 0 : Int)
def valid (n : Nat) (value : Int) : Prop := 1 ≤ value ∧ value ≤ 2 * (n : Int)
instance (n : Nat) (value : Int) : Decidable (valid n value) := by
  unfold valid
  infer_instance
def outerPrefix (n : Nat) (inner : List Nat) (target : Int) (first : Nat) : List Int :=
  ((List.range' first (n - first)).map (forcedValue n inner target)).takeWhile
    (fun value => decide (valid n value))

theorem prefix_step (n : Nat) (inner : List Nat) (target : Int) (first : Nat)
    (active : first < n) :
    outerPrefix n inner target first =
      if valid n (forcedValue n inner target first)
      then forcedValue n inner target first :: outerPrefix n inner target (first + 1) else [] := by
  unfold outerPrefix
  rw [show n - first = (n - (first + 1)) + 1 by omega, List.range'_succ]
  simp only [List.map_cons, List.takeWhile_cons, decide_eq_true_eq]

theorem prefix_done (n : Nat) (inner : List Nat) (target : Int) (first : Nat) (done : n ≤ first) :
    outerPrefix n inner target first = [] := by
  simp [outerPrefix, Nat.sub_eq_zero_of_le done]

theorem prefix_valid (n : Nat) (inner : List Nat) (target : Int) (first : Nat)
    (value : Int) (member : value ∈ outerPrefix n inner target first) : valid n value := by
  have accepted : decide (valid n value) = true :=
    List.mem_takeWhile_imp (p := fun item => decide (valid n item)) member
  exact of_decide_eq_true accepted

theorem prefix_length (n : Nat) (inner : List Nat) (target : Int) (first : Nat) :
    (outerPrefix n inner target first).length ≤ n - first := by
  have part : (outerPrefix n inner target first).Sublist
      ((List.range' first (n - first)).map (forcedValue n inner target)) :=
    List.takeWhile_sublist _
  simpa only [List.length_map, List.length_range'] using part.length_le

theorem prefix_full (n : Nat) (inner : List Nat) (target : Int) (first : Nat)
    (full : (outerPrefix n inner target first).length = n - first) :
    outerPrefix n inner target first =
      (List.range' first (n - first)).map (forcedValue n inner target) := by
  apply (List.takeWhile_sublist _).eq_of_length
  simpa only [List.length_map, List.length_range'] using full

theorem prefix_complete_iff (n : Nat) (inner : List Nat) (target : Int) (first : Nat) :
    (outerPrefix n inner target first).length = n - first ↔
      ∀ index ∈ List.range' first (n - first), valid n (forcedValue n inner target index) := by
  constructor
  · intro full index member
    apply prefix_valid n inner target first
    rw [prefix_full n inner target first full]
    exact List.mem_map.mpr ⟨index, member, rfl⟩
  · intro all
    have accepted : ∀ value ∈ (List.range' first (n - first)).map (forcedValue n inner target),
        decide (valid n value) = true := by
      intro value member
      obtain ⟨index, belongs, equal⟩ := List.mem_map.mp member
      subst value
      exact decide_eq_true (all index belongs)
    have same := (List.takeWhile_eq_self_iff).mpr accepted
    simpa only [outerPrefix, List.length_map, List.length_range'] using congrArg List.length same

theorem found (base : Mutable.Heap) (values : List Int) :
    (working base values)[base.length]? = some (.list (encodeInts values)) := by simp [working]

theorem prefix_found (base : Mutable.Heap) (values : List Int) (address : Nat)
    (object : Mutable.Object) (read : base[address]? = some object) :
    (working base values)[address]? = some object := by
  rw [working, List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
  exact read

def valueExpression : Expr :=
  .binOp (.binOp (.name "target") .sub (.subscript (.name "inner") (.name "index"))) .sub
    (.subscript (.name "inner")
      (.binOp (.binOp (.name "index") .add (.constant (.int 1))) .mod (.name "n")))
def condition : Expr := .boolOp .or
  [.compare (.name "value") [(.lt, .constant (.int 1))],
   .compare (.name "value") [(.gt, .binOp (.constant (.int 2)) .mult (.name "n"))]]
def body : List Stmt :=
  [.assign [.name "value"] valueExpression, .ifThen condition [.breakLoop] [],
   .expr (.call (.attribute (.name "outer") "append") [.name "value"])]

structure Ready (n : Nat) (target : Int) (innerAddress outerAddress : Nat)
    (env : HeapCalls.Env) : Prop where
  getN : env "n" = some (number n)
  getTarget : env "target" = some (integer target)
  getInner : env "inner" = some (.ref innerAddress)
  getOuter : env "outer" = some (.ref outerAddress)

def Keeps (before after : HeapCalls.Env) : Prop :=
  ∀ name, name ≠ "index" → name ≠ "value" → after name = before name

theorem value_result (program : Module) (n : Nat) (inner : List Nat) (size : inner.length = n)
    (target : Int) (index : Nat) (inside : index < n) (heap : Mutable.Heap)
    (env : HeapCalls.Env) (innerAddress : Nat)
    (getInner : heap[innerAddress]? = some (.tuple (encode inner)))
    (localInner : env "inner" = some (.ref innerAddress))
    (localTarget : env "target" = some (integer target))
    (localN : env "n" = some (number n)) (localIndex : env "index" = some (number index)) :
    Evaluates program env valueExpression heap
      (integer (forcedValue n inner target index)) heap := by
  have currentInside : index < inner.length := by rw [size]; exact inside
  have nextInside : (index + 1) % n < inner.length := by
    rw [size]
    exact Nat.mod_lt _ (by omega)
  have nextIndex : Evaluates program env
      (.binOp (.binOp (.name "index") .add (.constant (.int 1))) .mod (.name "n")) heap
      (number ((index + 1) % n)) heap :=
    Evaluates.binary (av := number (index + 1)) (bv := number n) (middle := heap)
      (afterRight := heap)
      (Evaluates.binary (Evaluates.lookup localIndex) Evaluates.constant
        (by simp [Mutable.binary, scalarBinary, number])) (Evaluates.lookup localN)
      (by simp [Mutable.binary, scalarBinary, number,
        show 0 < n by omega, show n ≠ 0 by omega])
  have current := index_evaluates program heap env "inner" innerAddress index true inner
    ((inner[index]?).getD 0) (.name "index") localInner (Evaluates.lookup localIndex)
    (by intros a b c impossible; cases impossible) getInner
    (by rw [List.getElem?_eq_getElem currentInside]; rfl)
  have next := index_evaluates program heap env "inner" innerAddress ((index + 1) % n) true inner
    ((inner[(index + 1) % n]?).getD 0) _ localInner nextIndex
    (by intros a b c impossible; cases impossible) getInner
    (by rw [List.getElem?_eq_getElem nextInside]; rfl)
  exact Evaluates.binary (middle := heap) (afterRight := heap)
    (av := integer (target - ((inner[index]?).getD 0 : Int)))
    (Evaluates.binary (middle := heap) (afterRight := heap)
      (Evaluates.lookup localTarget) current rfl) next rfl

theorem condition_result (program : Module) (n : Nat) (value : Int)
    (heap : Mutable.Heap) (env : HeapCalls.Env)
    (localValue : env "value" = some (integer value)) (localN : env "n" = some (number n)) :
    Evaluates program env condition heap (.scalar (.bool (decide (¬ valid n value)))) heap := by
  have low : Evaluates program env (.compare (.name "value") [(.lt, .constant (.int 1))]) heap
      (.scalar (.bool (decide (value < 1)))) heap :=
    Evaluates.compare (middle := heap) (afterRight := heap)
      (Evaluates.lookup localValue) Evaluates.constant
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  have high : Evaluates program env
      (.compare (.name "value") [(.gt, .binOp (.constant (.int 2)) .mult (.name "n"))]) heap
      (.scalar (.bool (decide (2 * (n : Int) < value)))) heap :=
    Evaluates.compare (middle := heap) (afterRight := heap)
      (Evaluates.lookup localValue)
      (Evaluates.binary (middle := heap) (afterRight := heap)
        (value := integer (2 * n)) Evaluates.constant (Evaluates.lookup localN) rfl)
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp])
  have bad : (¬ valid n value) ↔ value < 1 ∨ 2 * (n : Int) < value := by
    unfold valid
    omega
  by_cases below : value < 1
  · simpa only [bad, below, true_or, decide_true] using
      (Evaluates.boolean_stop (op := .or)
        (rest := [.compare (.name "value")
          [(.gt, .binOp (.constant (.int 2)) .mult (.name "n"))]])
        (by simpa only [below, decide_true] using low) rfl rfl)
  · change Evaluates program env (.boolOp .or _) heap _ heap
    apply Evaluates.boolean_next (flag := false)
      (by simpa only [below, decide_false] using low) rfl rfl
    simpa only [bad, below, false_or] using Evaluates.boolean_last high rfl

theorem loop_result (program : Module) (n : Nat) (inner : List Nat) (size : inner.length = n)
    (target : Int) (position : Nat) (before : position ≤ n) (base : Mutable.Heap)
    (values : List Int) (env : HeapCalls.Env) (innerAddress : Nat)
    (getInner : base[innerAddress]? = some (.tuple (encode inner)))
    (ready : Ready n target innerAddress base.length env) :
    ∃ finalEnv, BlockContinues program env [.rangeStepLoop "index" position n 1 body []]
      (working base values) finalEnv
        (working base (values ++ outerPrefix n inner target position)) ∧
      Keeps env finalEnv := by
  by_cases active : position < n
  · let indexed := setLocal env "index" (number position)
    let valueEnv := setLocal indexed "value" (integer (forcedValue n inner target position))
    have nextReady : Ready n target innerAddress base.length valueEnv := by
      constructor
      · simpa [valueEnv, indexed, setLocal] using ready.getN
      · simpa [valueEnv, indexed, setLocal] using ready.getTarget
      · simpa [valueEnv, indexed, setLocal] using ready.getInner
      · simpa [valueEnv, indexed, setLocal] using ready.getOuter
    have calculated := value_result program n inner size target position active
      (working base values) indexed innerAddress (prefix_found base values innerAddress _ getInner)
      (by simpa [indexed, setLocal] using ready.getInner)
      (by simpa [indexed, setLocal] using ready.getTarget)
      (by simpa [indexed, setLocal] using ready.getN) rfl
    have tested := condition_result program n (forcedValue n inner target position)
      (working base values) valueEnv rfl nextReady.getN
    by_cases good : valid n (forcedValue n inner target position)
    · obtain ⟨finalEnv, continued, kept⟩ := loop_result program n inner size target (position + 1)
        (by omega) base (values ++ [forcedValue n inner target position]) valueEnv
        innerAddress getInner nextReady
      have appended := Evaluates.append (module := program) (globals := [])
        (Evaluates.lookup nextReady.getOuter) (found base values)
        (Evaluates.lookup (show valueEnv "value" = _ from rfl)) (found base values)
      have wrote : Evaluates program valueEnv
          (.call (.attribute (.name "outer") "append") [.name "value"])
          (working base values) (.scalar .none)
          (working base (values ++ [forcedValue n inner target position])) := by
        simpa [working, encodeInts, List.map_append, List.set_append_right] using appended
      refine ⟨finalEnv, ?_, ?_⟩
      · simp only [prefix_step n inner target position active, good, if_true]
        apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        apply (BlockContinues.assign calculated).append
        apply BlockContinues.branch_next (flag := false)
          (by simpa only [good, not_true_eq_false, decide_false] using tested) rfl
        apply (BlockContinues.discard wrote).append
        apply BlockContinues.loop_resume
        simpa only [Nat.cast_add, Nat.cast_one, List.append_assoc, List.singleton_append]
          using continued
      · intro name notIndex notValue
        rw [kept name notIndex notValue]
        simp [valueEnv, indexed, setLocal, notIndex, notValue]
    · refine ⟨valueEnv, ?_, ?_⟩
      · simp only [prefix_step n inner target position active, good, if_false, List.append_nil]
        apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        apply (BlockContinues.assign calculated).append
        apply BlockContinues.branch_next (flag := true)
          (by simpa only [good, not_false_eq_true, decide_true] using tested) rfl
        exact BlockContinues.break_loop (next := .rangeStepLoop "index"
          ((position : Int) + 1) n 1 body []) (rest := []) rfl .nil
      · intro name notIndex notValue
        simp [valueEnv, indexed, setLocal, notIndex, notValue]
  · refine ⟨env, ?_, ?_⟩
    · simp only [prefix_done n inner target position (by omega), List.append_nil]
      exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
    · intro name _ _; rfl
termination_by n - position
decreasing_by omega

end ProjectEulerStatements.MagicRingOuterCalls
