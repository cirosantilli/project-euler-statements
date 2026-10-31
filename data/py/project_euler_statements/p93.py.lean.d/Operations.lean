import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».Finish

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.eval_ops
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
set_option Elab.async false

/-- Every input tuple may be shared with the caller or with the other operand. -/
theorem result (a b : Pair) (left right : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (foundA : heap[left]? = some (object a)) (foundB : heap[right]? = some (object b)) :
    ∃ extra, ReturnsValue program "eval_ops" [.ref left, .ref right] heap (.ref (listAddress heap))
      (heap ++ extra) globals ∧ Heap.ListFound (heap ++ extra) (listAddress heap) (reference a b) := by
  let args := ((findFunctionIn program.body "eval_ops").getD ([], [])).1
  let source := ((findFunctionIn program.body "eval_ops").getD ([], [])).2
  let entry := functionEnv args source [.ref left, .ref right] globals
  have getA : entry "a" = some (.ref left) := by cases globals <;> rfl
  have getB : entry "b" = some (.ref right) := by cases globals <;> rfl
  let first := assignNames entry ["numerator_a", "denominator_a"] [number a.1, number a.2]
  let second := assignNames first ["numerator_b", "denominator_b"] [number b.1, number b.2]
  let multiplied := setLocal second "denominator" (number (a.2*b.2))
  have ready : Ready multiplied a b := by
    constructor <;> simp [multiplied, second, first, assignNames, setLocal]
  let complete := setLocal multiplied "out" (.ref (listAddress heap))
  have readyOut : Ready complete a b := by
    constructor <;> simp [complete, multiplied, second, first, assignNames, setLocal]
  obtain ⟨extra, finished, finalFound⟩ := finish_result heap a b complete globals readyOut (by simp [complete, setLocal])
  refine ⟨extra, ?_, finalFound⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.unpack (names := ["numerator_a", "denominator_a"])
    (items := [number a.1, number a.2]) (afterUnpack := heap) rfl (Evaluates.lookup getA)
    (by simp [Mutable.sequence, foundA, object, Heap.object]) rfl
  apply BlockReturns.unpack (names := ["numerator_b", "denominator_b"])
    (items := [number b.1, number b.2]) (afterUnpack := heap) rfl
    (Evaluates.lookup (by simpa [first, assignNames, setLocal] using getB))
    (by simp [Mutable.sequence, foundB, object, Heap.object]) rfl
  apply BlockReturns.assign
    (times (x := a.2) (y := b.2) (Evaluates.lookup (by simp [assignNames, setLocal]))
      (Evaluates.lookup (by simp [assignNames, setLocal])))
  apply BlockReturns.assign (initial a b heap multiplied globals ready)
  exact finished

def Verified (a b : Pair) (left right : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals) : Prop :=
  ∃ extra, ReturnsValue program "eval_ops" [.ref left, .ref right] heap (.ref (listAddress heap))
    (heap ++ extra) globals ∧ Heap.ListFound (heap ++ extra) (listAddress heap) (reference a b)

theorem verified (a b : Pair) (left right : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (foundA : heap[left]? = some (object a)) (foundB : heap[right]? = some (object b)) :
    Verified a b left right heap globals := result a b left right heap globals foundA foundB

/-- The source's fresh list represents exactly the defined rational operations. -/
theorem values (a b : Pair) (left right : Nat) (heap : Mutable.Heap) (globals : Mutable.Globals)
    (positiveA : 0 < a.2) (positiveB : 0 < b.2)
    (foundA : heap[left]? = some (object a)) (foundB : heap[right]? = some (object b)) :
    ∃ extra pairs, ReturnsValue program "eval_ops" [.ref left, .ref right] heap (.ref (listAddress heap))
      (heap ++ extra) globals ∧ Heap.ListFound (heap ++ extra) (listAddress heap) pairs ∧
      (∀ pair ∈ pairs, 0 < pair.2) ∧
      pairs.map value = ProjectEulerSolutions.ArithmeticExpressions.operations (value a) (value b) := by
  obtain ⟨extra, ran, found⟩ := result a b left right heap globals foundA foundB
  exact ⟨extra, reference a b, ran, found, fun pair member => reference_positive a b pair positiveA positiveB member,
    reference_values a b positiveA positiveB⟩

end data.«project-euler-statements».data.py.project_euler_statements.p93.eval_ops
