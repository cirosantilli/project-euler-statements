import ProjectEulerStatements.Lib.MagicRingTextCalls
import ProjectEulerStatements.Lib.MagicRingSearch

/-! The reference checks successive line totals and stops at the first mismatch. -/
namespace ProjectEulerStatements.MagicRingLineCalls
open FormalSW.PyAst HeapCalls MagicRing MagicRingTextCalls
set_option Elab.async false

def lineTotal {n : Nat} (ring : Ring n) (index : Nat) : Nat :=
  (ring.outer[index]?).getD 0 + (ring.inner[index]?).getD 0 +
    (ring.inner[(index + 1) % n]?).getD 0

def checks {n : Nat} (ring : Ring n) (target first : Nat) : Bool :=
  (List.range' first (n - first)).all (fun index => decide (lineTotal ring index = target))

theorem checks_step {n : Nat} (ring : Ring n) (target first : Nat) (active : first < n) :
    checks ring target first =
      (decide (lineTotal ring first = target) && checks ring target (first + 1)) := by
  unfold checks
  rw [show n - first = (n - (first + 1)) + 1 by omega, List.range'_succ]
  rfl

theorem checks_done {n : Nat} (ring : Ring n) (target first : Nat) (done : n ≤ first) :
    checks ring target first = true := by simp [checks, Nat.sub_eq_zero_of_le done]

theorem checks_iff {n : Nat} (ring : Ring n) (target first : Nat) :
    checks ring target first = true ↔
      ∀ index, first ≤ index → index < n → lineTotal ring index = target := by
  simp only [checks, List.all_eq_true, decide_eq_true_eq, List.mem_range'_1]
  constructor
  · intro all index lower upper
    exact all index ⟨lower, by omega⟩
  · intro all index bounds
    exact all index bounds.1 (by omega)

theorem lineTotal_cycle {n : Nat} (ring : Ring n) (index : Nat) (inside : index < n) :
    lineTotal ring index =
      let triple := (cycle ring.outer ring.inner)[index]'(by rw [cycle_length]; exact inside)
      triple.1 + triple.2.1 + triple.2.2 := by
  rw [cycle_getElem ring index inside]
  simp only [lineTotal,
    List.getElem?_eq_getElem (show index < ring.outer.length by
      rw [ring.outer_length]; exact inside),
    List.getElem?_eq_getElem (show index < ring.inner.length by
      rw [ring.inner_length]; exact inside),
    List.getElem?_eq_getElem (show (index + 1) % n < ring.inner.length by
      rw [ring.inner_length]; exact Nat.mod_lt _ (by omega)), Option.getD_some]

theorem checks_magic {n : Nat} (ring : Ring n) (size : 2 ≤ n) :
    checks ring (firstSum ring) 1 = true ↔ Magic ring (firstSum ring) := by
  rw [checks_iff]
  constructor
  · intro all triple member
    obtain ⟨index, inside, rfl⟩ := List.getElem_of_mem member
    have bound : index < n := by simpa only [cycle_length] using inside
    rw [← lineTotal_cycle ring index bound]
    by_cases zero : index = 0
    · subst index
      simp [lineTotal, firstSum, Nat.mod_eq_of_lt (by omega : 1 < n),
        List.headD_eq_head?_getD, List.head?_eq_getElem?]
    · exact all index (by omega) bound
  · intro magic index lower upper
    rw [lineTotal_cycle ring index upper]
    exact magic _ (List.getElem_mem (by rw [cycle_length]; exact upper))

def lineExpression : Expr :=
  .binOp (.binOp (.subscript (.name "outer") (.name "index")) .add
    (.subscript (.name "inner") (.name "index"))) .add
    (.subscript (.name "inner")
      (.binOp (.binOp (.name "index") .add (.constant (.int 1))) .mod (.name "n")))

def condition : Expr := .compare lineExpression [(.notEq, .name "target")]
def body : List Stmt :=
  [.ifThen condition [.assign [.name "magic"] (.constant (.bool false)), .breakLoop] []]

structure Ready (n target outerAddress innerAddress : Nat) (env : HeapCalls.Env) : Prop where
  getN : env "n" = some (number n)
  getTarget : env "target" = some (number target)
  getOuter : env "outer" = some (.ref outerAddress)
  getInner : env "inner" = some (.ref innerAddress)
  getMagic : env "magic" = some (.scalar (.bool true))

def Keeps (before after : HeapCalls.Env) : Prop :=
  ∀ name, name ≠ "index" → name ≠ "magic" → after name = before name

theorem line_result (program : Module) {n : Nat} (ring : Ring n) (index : Nat)
    (inside : index < n) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (outerAddress innerAddress : Nat)
    (getOuter : heap[outerAddress]? = some (.list (encode ring.outer)))
    (getInner : heap[innerAddress]? = some (.tuple (encode ring.inner)))
    (localOuter : env "outer" = some (.ref outerAddress))
    (localInner : env "inner" = some (.ref innerAddress))
    (localIndex : env "index" = some (number index)) (localN : env "n" = some (number n)) :
    Evaluates program env lineExpression heap (number (lineTotal ring index)) heap := by
  have outerInside : index < ring.outer.length := by rw [ring.outer_length]; exact inside
  have innerInside : index < ring.inner.length := by rw [ring.inner_length]; exact inside
  have nextInside : (index + 1) % n < ring.inner.length := by
    rw [ring.inner_length]
    exact Nat.mod_lt _ (by omega)
  have nextIndex : Evaluates program env
      (.binOp (.binOp (.name "index") .add (.constant (.int 1))) .mod (.name "n")) heap
      (number ((index + 1) % n)) heap := by
    exact Evaluates.binary (av := number (index + 1)) (bv := number n) (middle := heap)
      (afterRight := heap)
      (Evaluates.binary (Evaluates.lookup localIndex) Evaluates.constant
        (by simp [Mutable.binary, scalarBinary, number])) (Evaluates.lookup localN)
      (by simp [Mutable.binary, scalarBinary, number,
        show 0 < n by omega, show n ≠ 0 by omega])
  have outerRead := index_evaluates program heap env "outer" outerAddress index false ring.outer
    ((ring.outer[index]?).getD 0) (.name "index") localOuter (Evaluates.lookup localIndex)
    (by intros a b c impossible; cases impossible) getOuter
    (by rw [List.getElem?_eq_getElem outerInside]; rfl)
  have innerRead := index_evaluates program heap env "inner" innerAddress index true ring.inner
    ((ring.inner[index]?).getD 0) (.name "index") localInner (Evaluates.lookup localIndex)
    (by intros a b c impossible; cases impossible) getInner
    (by rw [List.getElem?_eq_getElem innerInside]; rfl)
  have nextRead := index_evaluates program heap env "inner" innerAddress
    ((index + 1) % n) true ring.inner ((ring.inner[(index + 1) % n]?).getD 0) _
    localInner nextIndex (by intros a b c impossible; cases impossible) getInner
    (by rw [List.getElem?_eq_getElem nextInside]; rfl)
  exact Evaluates.binary (middle := heap) (afterRight := heap)
    (av := number ((ring.outer[index]?).getD 0 + (ring.inner[index]?).getD 0))
    (Evaluates.binary (middle := heap) (afterRight := heap) outerRead innerRead
      (by simp [Mutable.binary, scalarBinary, number])) nextRead
    (by simp [Mutable.binary, scalarBinary, number, lineTotal])

private theorem exit_loop (program : Module) (env : HeapCalls.Env) (next : Stmt)
    (heap : Mutable.Heap) :
    BlockContinues program env [.breakLoop, .loopResume next] heap env heap := by
  intro following anchors stack
  exact .next (by simp [step, Calls.loopTarget]) .refl

private theorem branch_tail
    {module : Module} {env finalEnv : HeapCalls.Env} {heap finalHeap : Mutable.Heap}
    {condition : Expr} {flag : Bool} {yes no tail : List Stmt}
    (evaluated : Evaluates module env condition heap (.scalar (.bool flag)) heap)
    (rest : BlockContinues module env ((if flag then yes else no) ++ tail)
      heap finalEnv finalHeap) :
    BlockContinues module env (.ifThen condition yes no :: tail) heap finalEnv finalHeap := by
  intro following anchors stack
  exact .next rfl ((evaluated anchors _).trans
    (.next (by simp [step, run, Mutable.truth, scalarTruth, List.append_assoc])
      (rest following anchors stack)))

theorem loop_result (program : Module) {n : Nat} (ring : Ring n) (target first : Nat)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (outerAddress innerAddress : Nat)
    (getOuter : heap[outerAddress]? = some (.list (encode ring.outer)))
    (getInner : heap[innerAddress]? = some (.tuple (encode ring.inner)))
    (ready : Ready n target outerAddress innerAddress env) :
    ∃ finalEnv, BlockContinues program env
      [.rangeStepLoop "index" first n 1 body []] heap finalEnv heap ∧
      finalEnv "magic" = some (.scalar (.bool (checks ring target first))) ∧
      Keeps env finalEnv := by
  by_cases active : first < n
  · let indexed := setLocal env "index" (number first)
    have nextReady : Ready n target outerAddress innerAddress indexed := by
      constructor
      · simpa [indexed, setLocal] using ready.getN
      · simpa [indexed, setLocal] using ready.getTarget
      · simpa [indexed, setLocal] using ready.getOuter
      · simpa [indexed, setLocal] using ready.getInner
      · simpa [indexed, setLocal] using ready.getMagic
    have tested : Evaluates program indexed condition heap
        (.scalar (.bool (decide (lineTotal ring first ≠ target)))) heap := by
      apply Evaluates.compare (middle := heap) (afterRight := heap)
        (av := number (lineTotal ring first)) (bv := number target)
      · exact line_result program ring first active heap indexed outerAddress innerAddress
          getOuter getInner nextReady.getOuter nextReady.getInner rfl nextReady.getN
      · exact Evaluates.lookup nextReady.getTarget
      · simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    by_cases equal : lineTotal ring first = target
    · obtain ⟨finalEnv, rest, magic, kept⟩ := loop_result program ring target (first + 1)
        heap indexed outerAddress innerAddress getOuter getInner nextReady
      refine ⟨finalEnv, ?_, ?_, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        apply branch_tail (flag := false) (by simpa [equal] using tested)
        change BlockContinues program indexed
          [.loopResume (.rangeStepLoop "index" ((first : Int) + 1) n 1 body [])]
          heap finalEnv heap
        apply BlockContinues.loop_resume
        simpa only [Nat.cast_add, Nat.cast_one] using rest
      · simpa only [checks_step ring target first active, equal, decide_true,
          Bool.true_and] using magic
      · intro name notIndex notMagic
        rw [kept name notIndex notMagic]
        simp [indexed, setLocal, notIndex]
    · let failed := setLocal indexed "magic" (.scalar (.bool false))
      refine ⟨failed, ?_, ?_, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        apply branch_tail (flag := true) (by simpa [equal] using tested)
        apply (BlockContinues.assign Evaluates.constant).append
        exact exit_loop program failed _ heap
      · simp [failed, setLocal, checks_step ring target first active, equal]
      · intro name notIndex notMagic
        simp [failed, indexed, setLocal, notIndex, notMagic]
  · refine ⟨env, ?_, ?_, ?_⟩
    · exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) .nil
    · simpa only [checks_done ring target first (by omega)] using ready.getMagic
    · intro name _ _; rfl
termination_by n - first
decreasing_by omega

end ProjectEulerStatements.MagicRingLineCalls
