import data.«project-euler-statements».data.py.project_euler_statements.«p68.assignment.source»
import ProjectEulerStatements.Lib.MagicRingReferenceScan

namespace data.«project-euler-statements».data.py.project_euler_statements.p68
open FormalSW.PyAst HeapCalls ProjectEulerStatements MagicRing MagicRingTextCalls
set_option Elab.async false

structure SearchReady (n : Nat) (digits : Int) (best : String) (env : HeapCalls.Env) : Prop where
  getN : env "n" = some (number n)
  getDigits : env "digits" = some (.scalar (.int digits))
  getBest : env "best" = some (string best)

abbrev visit {n : Nat} (ring : Ring n) (digits : Int) (best : String) : String :=
  referenceVisit ring digits best

abbrev canonicalCondition : Expr :=
  .compare (.subscript (.name "outer") (.constant (.int 0)))
    [(.notEq, .builtinCall .min [.name "outer"])]
abbrev firstExpression : Expr :=
  .binOp (.binOp (.subscript (.name "outer") (.constant (.int 0))) .add
    (.subscript (.name "inner") (.constant (.int 0)))) .add
    (.subscript (.name "inner") (.constant (.int 1)))
abbrev rejectMagic : Stmt := .ifThen (.unaryOp .not (.name "magic")) [.continueLoop] []
abbrev textAssignment : Stmt := .assign [.name "text"]
  (.call (.name "ring_string") [.name "outer", .name "inner", .constant (.int 0)])

theorem candidate_code_source : permutationBody = splitCode ++
    [.ifThen canonicalCondition [.continueLoop] [],
     .assign [.name "target"] firstExpression,
     .assign [.name "magic"] (.constant (.bool true)), lineLoop,
     rejectMagic, textAssignment] ++ MagicRingRecordCalls.code := rfl

theorem first_result {n : Nat} (ring : Ring n) (size : 2 ≤ n)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (outerAddress innerAddress : Nat)
    (getOuter : heap[outerAddress]? = some (.list (encode ring.outer)))
    (getInner : heap[innerAddress]? = some (.tuple (encode ring.inner)))
    (localOuter : env "outer" = some (.ref outerAddress))
    (localInner : env "inner" = some (.ref innerAddress)) :
    Evaluates program env firstExpression heap (number (firstSum ring)) heap := by
  have outerZero : 0 < ring.outer.length := by rw [ring.outer_length]; omega
  have innerZero : 0 < ring.inner.length := by rw [ring.inner_length]; omega
  have innerOne : 1 < ring.inner.length := by rw [ring.inner_length]; omega
  have outerRead := index_evaluates program heap env "outer" outerAddress 0 false ring.outer
    ((ring.outer[0]?).getD 0) (.constant (.int 0)) localOuter Evaluates.constant
    (by intros a b c impossible; cases impossible) getOuter
    (by rw [List.getElem?_eq_getElem outerZero]; rfl)
  have innerRead := index_evaluates program heap env "inner" innerAddress 0 true ring.inner
    ((ring.inner[0]?).getD 0) (.constant (.int 0)) localInner Evaluates.constant
    (by intros a b c impossible; cases impossible) getInner
    (by rw [List.getElem?_eq_getElem innerZero]; rfl)
  have nextRead := index_evaluates program heap env "inner" innerAddress 1 true ring.inner
    ((ring.inner[1]?).getD 0) (.constant (.int 1)) localInner Evaluates.constant
    (by intros a b c impossible; cases impossible) getInner
    (by rw [List.getElem?_eq_getElem innerOne]; rfl)
  exact Evaluates.binary (middle := heap) (afterRight := heap)
    (av := number ((ring.outer[0]?).getD 0 + (ring.inner[0]?).getD 0))
    (Evaluates.binary (middle := heap) (afterRight := heap) outerRead innerRead
      (by simp [Mutable.binary, scalarBinary, number])) nextRead
    (by simp [Mutable.binary, scalarBinary, number, firstSum,
      List.headD_eq_head?_getD, List.head?_eq_getElem?])

theorem after_lines {n : Nat} (ring : Ring n) (size : 2 ≤ n) (digits : Int) (best : String)
    (canonical : Canonical ring) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (outerAddress innerAddress : Nat)
    (getOuter : heap[outerAddress]? = some (.list (encode ring.outer)))
    (getInner : heap[innerAddress]? = some (.tuple (encode ring.inner)))
    (localOuter : env "outer" = some (.ref outerAddress))
    (localInner : env "inner" = some (.ref innerAddress))
    (getMagic : env "magic" =
      some (.scalar (.bool (MagicRingLineCalls.checks ring (firstSum ring) 1))))
    (ready : SearchReady n digits best env) (next : Stmt) (following : List Stmt)
    (answer : Mutable.Value)
    (post : ∀ nextEnv nextHeap, SearchReady n digits (visit ring digits best) nextEnv →
      ∃ finalHeap, BlockReturns program nextEnv (next :: following) nextHeap answer finalHeap) :
    ∃ finalHeap, BlockReturns program env
      ([rejectMagic, textAssignment] ++ MagicRingRecordCalls.code ++
        [.loopResume next] ++ following)
      heap answer finalHeap := by
  have tested : Evaluates program env (.unaryOp .not (.name "magic")) heap
      (.scalar (.bool (!MagicRingLineCalls.checks ring (firstSum ring) 1))) heap :=
    Evaluates.unary (Evaluates.lookup getMagic) rfl
  by_cases magic : Magic ring (firstSum ring)
  · have checked : MagicRingLineCalls.checks ring (firstSum ring) 1 = true :=
      (MagicRingLineCalls.checks_magic ring size).mpr magic
    have serialized : Evaluates program env
        (.call (.name "ring_string") [.name "outer", .name "inner", .constant (.int 0)]) heap
        (string (text ring.outer ring.inner)) (working heap (pieces ring 0 n)) := by
      have result := ring_string.result ring 0 heap outerAddress innerAddress getOuter getInner
      have same : textFrom ring.outer ring.inner 0 = text ring.outer ring.inner := by
        rw [textFrom_eq_rotated, rotate_zero]
      exact Evaluates.call (.cons (Evaluates.lookup localOuter)
        (.cons (Evaluates.lookup localInner) (.cons Evaluates.constant .nil))) (same ▸ result)
    let textEnv := setLocal env "text" (string (text ring.outer ring.inner))
    obtain ⟨finalEnv, recorded, getBest, kept⟩ := MagicRingRecordCalls.result program
      (text ring.outer ring.inner) best digits (working heap (pieces ring 0 n)) textEnv rfl
      (by simpa [textEnv, setLocal] using ready.getBest)
      (by simpa [textEnv, setLocal] using ready.getDigits)
    have finalReady : SearchReady n digits (visit ring digits best) finalEnv := by
      constructor
      · rw [kept "n" (by decide)]
        simpa [textEnv, setLocal] using ready.getN
      · rw [kept "digits" (by decide)]
        simpa [textEnv, setLocal] using ready.getDigits
      · simpa only [visit, referenceVisit, canonical, magic, and_self, if_true] using getBest
    obtain ⟨finalHeap, continued⟩ := post finalEnv (working heap (pieces ring 0 n)) finalReady
    refine ⟨finalHeap, ?_⟩
    apply BlockReturns.branch (flag := false)
      (by simpa only [checked, Bool.not_true] using tested) rfl
    apply BlockReturns.assign serialized
    exact recorded.returns (BlockReturns.loop_resume continued)
  · have checked : MagicRingLineCalls.checks ring (firstSum ring) 1 = false := by
      cases value : MagicRingLineCalls.checks ring (firstSum ring) 1
      · rfl
      · exact False.elim (magic ((MagicRingLineCalls.checks_magic ring size).mp value))
    have same : visit ring digits best = best := by
      simp only [visit, referenceVisit, magic, and_false, if_false]
    obtain ⟨finalHeap, continued⟩ := post env heap (by simpa only [same] using ready)
    refine ⟨finalHeap, ?_⟩
    apply BlockReturns.branch (flag := true)
      (by simpa only [checked, Bool.not_false] using tested) rfl
    exact BlockReturns.continue_loop (next := next) (following := following) rfl continued

theorem after_split {n : Nat} (ring : Ring n) (size : 2 ≤ n) (digits : Int) (best : String)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (outerAddress innerAddress : Nat)
    (getOuter : heap[outerAddress]? = some (.list (encode ring.outer)))
    (getInner : heap[innerAddress]? = some (.tuple (encode ring.inner)))
    (localOuter : env "outer" = some (.ref outerAddress))
    (localInner : env "inner" = some (.ref innerAddress))
    (ready : SearchReady n digits best env) (next : Stmt) (following : List Stmt)
    (answer : Mutable.Value)
    (post : ∀ nextEnv nextHeap, SearchReady n digits (visit ring digits best) nextEnv →
      ∃ finalHeap, BlockReturns program nextEnv (next :: following) nextHeap answer finalHeap) :
    ∃ finalHeap, BlockReturns program env
      (permutationBody.drop 2 ++ [.loopResume next] ++ following) heap answer finalHeap := by
  obtain ⟨flag, tested, canonical⟩ := MagicRingMinimumCalls.canonical_condition program ring
    (by omega) heap env outerAddress localOuter getOuter
  by_cases good : Canonical ring
  · have flagFalse : flag = false := canonical.mpr good
    let targetEnv := setLocal env "target" (number (firstSum ring))
    let magicEnv := setLocal targetEnv "magic" (.scalar (.bool true))
    have lineReady : MagicRingLineCalls.Ready n (firstSum ring)
        outerAddress innerAddress magicEnv := by
      constructor
      · simpa [magicEnv, targetEnv, setLocal] using ready.getN
      · rfl
      · simpa [magicEnv, targetEnv, setLocal] using localOuter
      · simpa [magicEnv, targetEnv, setLocal] using localInner
      · rfl
    obtain ⟨checkedEnv, checked, getMagic, kept⟩ := lines.result ring (firstSum ring) heap magicEnv
      outerAddress innerAddress getOuter getInner lineReady
    have checkedReady : SearchReady n digits best checkedEnv := by
      constructor
      · rw [kept "n" (by decide) (by decide)]
        exact lineReady.getN
      · rw [kept "digits" (by decide) (by decide)]
        simpa [magicEnv, targetEnv, setLocal] using ready.getDigits
      · rw [kept "best" (by decide) (by decide)]
        simpa [magicEnv, targetEnv, setLocal] using ready.getBest
    obtain ⟨finalHeap, rest⟩ := after_lines ring size digits best good heap checkedEnv
      outerAddress innerAddress getOuter getInner
      (by rw [kept "outer" (by decide) (by decide)]; exact lineReady.getOuter)
      (by rw [kept "inner" (by decide) (by decide)]; exact lineReady.getInner)
      getMagic checkedReady next following answer post
    refine ⟨finalHeap, ?_⟩
    rw [candidate_code_source]
    apply BlockReturns.branch (flag := false) (by simpa only [flagFalse] using tested) rfl
    apply BlockReturns.assign (first_result ring size heap env outerAddress innerAddress
      getOuter getInner localOuter localInner)
    apply BlockReturns.assign Evaluates.constant
    exact checked.returns rest
  · have flagTrue : flag = true := by
      cases flag
      · exact False.elim (good (canonical.mp rfl))
      · rfl
    have same : visit ring digits best = best := by
      simp only [visit, referenceVisit, good, false_and, if_false]
    obtain ⟨finalHeap, rest⟩ := post env heap (by simpa only [same] using ready)
    refine ⟨finalHeap, ?_⟩
    rw [candidate_code_source]
    apply BlockReturns.branch (flag := true) (by simpa only [flagTrue] using tested) rfl
    exact BlockReturns.continue_loop (next := next) (following := following) rfl rest

theorem candidate_result {n : Nat} (ring : Ring n) (size : 2 ≤ n) (digits : Int) (best : String)
    (heap : Mutable.Heap) (env : HeapCalls.Env) (address : Nat)
    (contents : heap[address]? = some (.tuple (encode (ring.outer ++ ring.inner))))
    (localValues : env "values" = some (.ref address)) (ready : SearchReady n digits best env)
    (next : Stmt) (following : List Stmt) (answer : Mutable.Value)
    (post : ∀ nextEnv nextHeap, SearchReady n digits (visit ring digits best) nextEnv →
      ∃ finalHeap, BlockReturns program nextEnv (next :: following) nextHeap answer finalHeap) :
    ∃ finalHeap, BlockReturns program env
      (permutationBody ++ [Calls.loopContinuation permutationBody next] ++ following)
      heap answer finalHeap := by
  have splitReady : SearchReady n digits best (splitEnv heap env) := by
    constructor
    · simpa [splitEnv, setLocal] using ready.getN
    · simpa [splitEnv, setLocal] using ready.getDigits
    · simpa [splitEnv, setLocal] using ready.getBest
  obtain ⟨finalHeap, rest⟩ := after_split ring size digits best (splitHeap heap ring)
    (splitEnv heap env) (heap.length + 1) (heap.length + 2)
    (split_outer heap ring) (split_inner heap ring) rfl rfl splitReady next following answer post
  refine ⟨finalHeap, ?_⟩
  have divided : permutationBody = splitCode ++ permutationBody.drop 2 := by
    rw [← split_code_source]
    exact (List.take_append_drop 2 permutationBody).symm
  rw [show Calls.loopContinuation permutationBody next = .loopResume next from rfl, divided]
  simpa only [List.append_assoc] using
    (split_result ring (by omega) heap env address contents localValues ready.getN).returns rest

end data.«project-euler-statements».data.py.project_euler_statements.p68
