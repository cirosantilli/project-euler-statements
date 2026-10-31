import data.«project-euler-statements».data.py.project_euler_statements.«p88.py.lean.d».ScanLoop

namespace data.«project-euler-statements».data.py.project_euler_statements.p88.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.ProductSumNumbers
set_option Elab.async false

/-- The repeated False list starts with no visited values, including index zero. -/
theorem allocate_seen (limit : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getLimit : env "limit" = some (number limit)) :
    Evaluates program env (.binOp (.list [.constant (.bool false)]) .mult
      (.binOp (.name "limit") .add (.constant (.int 1)))) heap (.ref (heap.length + 1))
      (scanHeap (heap ++ [.list [.scalar (.bool false)]]) limit ∅) := by
  let temporary := heap ++ [.list [.scalar (.bool false)]]
  apply Evaluates.binary (av := .ref heap.length) (bv := number (limit + 1))
    (middle := temporary) (afterRight := temporary)
  · exact Evaluates.list (.cons Evaluates.constant .nil)
  · exact Evaluates.binary (Evaluates.lookup getLimit) Evaluates.constant
      (by simp [Mutable.binary, scalarBinary, number])
  · have repeated := Mutable.Relocation.binary_mult_list_eval temporary heap.length
      [.scalar (.bool false)] (limit + 1) (by simp [temporary])
    simpa [temporary, Mutable.allocate, scanHeap, flags_empty] using repeated

def scanBase (heap : Mutable.Heap) (maxSize : Nat) : Mutable.Heap :=
  working (baseHeap heap maxSize) (table maxSize) ++ [.list [.scalar (.bool false)]]

def finalHeap (heap : Mutable.Heap) (maxSize : Nat) : Mutable.Heap :=
  scanHeap (scanBase heap maxSize) (2 * maxSize) ((table maxSize).drop 2).toFinset

/-- Complete reference execution, with every duplicate suppressed by its actual Boolean table. -/
theorem positive_result (maxSize : Nat) (large : 2 ≤ maxSize) (heap : Mutable.Heap) :
    ReturnsValue program "naive" [number maxSize] heap (number (answer maxSize)) (finalHeap heap maxSize) := by
  let entry := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number maxSize] []
  let ready := preparedEnv entry heap maxSize
  let tableHeap := working (baseHeap heap maxSize) (table maxSize)
  let allocated := setLocal ready "seen" (.ref (scanBase heap maxSize).length)
  let initialized := setLocal allocated "total" (number 0)
  have entryMax : entry "k_max" = some (number maxSize) := rfl
  have setup := prepare maxSize large heap entry rfl
  have seenAllocated : BlockContinues program ready [code[4]'(by decide)] tableHeap allocated
      (scanHeap (scanBase heap maxSize) (2 * maxSize) ∅) := by
    apply BlockContinues.assign
    simpa only [allocated, scanBase, List.length_append, List.length_singleton] using
      allocate_seen (2 * maxSize) tableHeap ready (by simp [ready, preparedEnv, setLocal])
  have zero : BlockContinues program allocated [code[5]'(by decide)]
      (scanHeap (scanBase heap maxSize) (2 * maxSize) ∅) initialized
      (scanHeap (scanBase heap maxSize) (2 * maxSize) ∅) := BlockContinues.assign Evaluates.constant
  have locals : ScanLocals initialized (2 * maxSize) (baseHeap heap maxSize).length
      (scanBase heap maxSize).length ∅ := by
    constructor
    · simp [initialized, allocated, ready, preparedEnv, setLocal]
    · simp [initialized, allocated, ready, preparedEnv, setLocal, baseHeap]
    · simp [initialized, allocated, setLocal]
    · simp [initialized, setLocal, number]
  have found : (scanBase heap maxSize)[(baseHeap heap maxSize).length]? =
      some (.list (encode (table maxSize))) := by
    simp [scanBase, working, List.append_assoc]
  obtain ⟨doneEnv, scanned, total⟩ := scan_result maxSize large (baseHeap heap maxSize).length
    (scanBase heap maxSize) found initialized locals
    (by simpa [initialized, allocated, ready, preparedEnv, setLocal] using entryMax)
  apply BlockReturns.function rfl rfl
  apply setup.returns
  apply seenAllocated.returns
  apply zero.returns
  apply scanned.returns
  exact BlockReturns.return_value (Evaluates.lookup total)

/-- Every signed bound terminates and returns the same mathematical distinct-minimum sum. -/
theorem result (maxSize : Int) (heap : Mutable.Heap) :
    ∃ afterHeap, ReturnsValue program "naive" [integer maxSize] heap
      (number (answer maxSize.toNat)) afterHeap := by
  by_cases small : maxSize < 2
  · refine ⟨heap, ?_⟩
    rw [answer_small maxSize.toNat (by omega)]
    exact small_result maxSize small heap
  · lift maxSize to Nat using (by omega : 0 ≤ maxSize)
    exact ⟨finalHeap heap maxSize, positive_result maxSize (by omega) heap⟩

end data.«project-euler-statements».data.py.project_euler_statements.p88.naive
