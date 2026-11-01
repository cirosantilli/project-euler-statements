import data.«project-euler-statements».data.py.project_euler_statements.«p82.py.lean.d».Row

namespace data.«project-euler-statements».data.py.project_euler_statements.p82
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P82
open ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

def addHeap (base : Mutable.Heap) (output : List Int) (scratch : Mutable.Heap) : Mutable.Heap :=
  base ++ [.list (encode output)] ++ scratch

abbrev sumElement : Expr := .binOp (.name "x") .add (.name "y")
abbrev sumTarget : Expr := .tuple [.name "x", .name "y"]
abbrev sumSources : List Expr := [.name "a", .name "b"]
abbrev sumComprehension : Expr := .listCompTargets sumElement [(sumTarget, .zipIterable sumSources, [])]
abbrev sumBody (address : Nat) : List Stmt :=
  [.assign [sumTarget] (.name "$formalsw.unpack"), .comprehensionAppend address sumElement]

theorem add_heap_read (base scratch : Mutable.Heap) (output : List Int) (address : Nat) (object : Mutable.Object)
    (found : base[address]? = some object) : (addHeap base output scratch)[address]? = some object := by
  unfold addHeap
  rw [List.append_assoc, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem sum_loop (base scratch : Mutable.Heap) (env : HeapCalls.Env) (left right output : List Int)
    (leftAddress rightAddress position : Nat)
    (getLeft : base[leftAddress]? = some (.list (encode left)))
    (getRight : base[rightAddress]? = some (.list (encode right))) (same : left.length = right.length) :
    ∃ after finalScratch, BlockContinues program env
      [.zipStepLoop "$formalsw.unpack" [.ref leftAddress, .ref rightAddress] position (sumBody base.length) []]
      (addHeap base output scratch) after
      (addHeap base (output ++ List.zipWith (· + ·) (left.drop position) (right.drop position)) finalScratch) := by
  let heap := addHeap base output scratch
  have read : zipItem [.ref leftAddress, .ref rightAddress] position heap =
      some (.ok (do let x ← left[position]?; let y ← right[position]?; pure [number x, number y]), heap) := by
    cases hx : left[position]? <;> cases hy : right[position]? <;>
      simp [zipItem, zipFields, sequenceValue, Mutable.sequence, add_heap_read base scratch output _ _ getLeft,
        add_heap_read base scratch output _ _ getRight, encode, hx, hy, Except.map, heap, number]
  by_cases active : position < left.length
  · have inRight : position < right.length := by omega
    let x := left[position]
    let y := right[position]
    let fields := [number x, number y]
    let more := scratch ++ [.tuple fields]
    let afterTuple := addHeap base output more
    let tupleEnv := setLocal env "$formalsw.unpack" (.ref heap.length)
    let assigned := assignNames tupleEnv ["x", "y"] fields
    have fetched : zipItem [.ref leftAddress, .ref rightAddress] position heap = some (.ok (some fields), heap) := by
      simpa [List.getElem?_eq_getElem active, List.getElem?_eq_getElem inRight, fields, x, y] using read
    have allocated : Mutable.allocateTuple fields heap = some (.ok (.ref heap.length), afterTuple) := by
      simp [Mutable.allocateTuple, fields, heap, afterTuple, more, addHeap, List.append_assoc, Except.map]
    have tupleFound : Mutable.sequence (.ref heap.length) afterTuple = some (.ok fields, afterTuple) := by
      have equal : afterTuple = heap ++ [.tuple fields] := by simp [afterTuple, heap, more, addHeap, List.append_assoc]
      simp [equal, Mutable.sequence]
    have unpacked : BlockContinues program tupleEnv [.assign [sumTarget] (.name "$formalsw.unpack")] afterTuple assigned afterTuple :=
      BlockContinues.unpack rfl (Evaluates.lookup rfl) tupleFound rfl
    have element : Evaluates program assigned sumElement afterTuple (number (x + y)) afterTuple :=
      Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) rfl
    have emitted : BlockContinues program assigned [.comprehensionAppend base.length sumElement] afterTuple assigned
        (addHeap base (output ++ [x + y]) more) := by
      have found : afterTuple[base.length]? = some (.list (encode output)) := by simp [afterTuple, addHeap, List.append_assoc]
      have step := BlockContinues.comprehension_append element found
      simpa [afterTuple, addHeap, encode, List.append_assoc] using step
    obtain ⟨after, finalScratch, continued⟩ := sum_loop base more assigned left right (output ++ [x + y])
      leftAddress rightAddress (position + 1) getLeft getRight same
    refine ⟨after, finalScratch, ?_⟩
    apply BlockContinues.zip_step fetched allocated
    simpa only [sumBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
      List.drop_eq_getElem_cons active, List.drop_eq_getElem_cons inRight, List.zipWith_cons_cons,
      x, y, List.append_assoc, List.singleton_append, Bool.false_or, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] using
      (unpacked.append emitted).append continued
  · have exhausted : zipItem [.ref leftAddress, .ref rightAddress] position heap = some (.ok none, heap) := by
      rw [read, List.getElem?_eq_none (by omega : left.length ≤ position)]
      rfl
    have gone : left.drop position = [] := List.drop_eq_nil_iff.mpr (by omega)
    refine ⟨env, scratch, ?_⟩
    simp only [gone, List.zipWith_nil_left, List.append_nil]
    exact BlockContinues.zip_done exhausted BlockContinues.nil
termination_by left.length - position
decreasing_by omega

theorem add_lists.result (heap : Mutable.Heap) (leftAddress rightAddress : Nat) (left right : List Int)
    (getLeft : heap[leftAddress]? = some (.list (encode left)))
    (getRight : heap[rightAddress]? = some (.list (encode right))) (same : left.length = right.length) :
    ∃ extra, ReturnsValue program "add_lists" [.ref leftAddress, .ref rightAddress] heap (.ref heap.length) (heap ++ extra) ∧
      (heap ++ extra)[heap.length]? = some (.list (encode (addLists left right))) := by
  let args : List Arg :=
    [⟨"a", some (.subscript (.name "list") (.name "int")), none⟩,
     ⟨"b", some (.subscript (.name "list") (.name "int")), none⟩]
  let entry := argumentEnv args [.ref leftAddress, .ref rightAddress]
  have tested : Evaluates program entry (.compare (.builtinCall .len [.name "a"]) [(.eq, .builtinCall .len [.name "b"])])
      heap (.scalar (.bool true)) heap := by
    apply Evaluates.compare (av := number left.length) (bv := number right.length) (middle := heap) (afterRight := heap)
    · exact Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil) (by simp [HeapCalls.primitive, Mutable.length, getLeft, encode])
    · exact Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil) (by simp [HeapCalls.primitive, Mutable.length, getRight, encode])
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, same]
  have captured : zipSources [.ref leftAddress, .ref rightAddress] heap =
      some (.ok [.ref leftAddress, .ref rightAddress], heap) := by
    simp [zipSources, List.mapM, List.mapM.loop, Mutable.sequence, getLeft, getRight, sequenceSource, Except.map]
  let masked := comprehensionTargetsEnv entry [(sumTarget, .zipIterable sumSources, [])]
  obtain ⟨after, scratch, loop⟩ := sum_loop heap [] masked left right [] leftAddress rightAddress 0 getLeft getRight same
  have comprehension : Evaluates program entry sumComprehension heap (.ref heap.length)
      (addHeap heap (List.zipWith (· + ·) left right) scratch) := by
    apply Evaluates.list_comp_targets_zip (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) captured
    simpa [masked, addHeap, sumBody, comprehensionTargetName, comprehensionTargetBody,
      comprehensionFilters, comprehensionTargetsBody] using loop
  refine ⟨[.list (encode (addLists left right))] ++ scratch, ?_, ?_⟩
  · apply BlockReturns.function (args := args) rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.conditional (flag := true) tested rfl
    simpa [addHeap, addLists, same, List.append_assoc] using comprehension
  · simp

end data.«project-euler-statements».data.py.project_euler_statements.p82
