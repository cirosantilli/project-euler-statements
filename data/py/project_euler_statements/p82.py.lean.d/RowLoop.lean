import data.«project-euler-statements».data.py.project_euler_statements.«p82.py.lean.d».Inputs
import ProjectEulerStatements.Lib.GridPathColumns

namespace data.«project-euler-statements».data.py.project_euler_statements.p82
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P82
open ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false
abbrev number (n : Int) : Mutable.Value := .scalar (.int n)

def rowHeap (base : Mutable.Heap) (output previous row : List Int) (scratch : Mutable.Heap) : Mutable.Heap :=
  base ++ [.list (encode output), .list (encode previous), .list (encode row)] ++ scratch

theorem rowHeap_output (base scratch : Mutable.Heap) (output previous row : List Int) :
    (rowHeap base output previous row scratch)[base.length]? = some (.list (encode output)) := by
  simp [rowHeap, List.append_assoc]

theorem rowHeap_append (base scratch : Mutable.Heap) (output previous row : List Int) (value : Int) :
    (rowHeap base output previous row scratch).set base.length (.list (encode (output ++ [value]))) =
      rowHeap base (output ++ [value]) previous row scratch := by
  simp [rowHeap, List.append_assoc]

abbrev rowElement : Expr := .builtinCall .min [.name "c", .binOp (.name "prev") .add (.name "v")]
abbrev rowStatements : List Stmt :=
  [.assign [.name "cur"] rowElement,
   .expr (.call (.attribute (.name "out") "append") [.name "cur"]),
   .assign [.name "prev"] (.name "cur")]
abbrev rowLoopBody : List Stmt :=
  [.assign [.tuple [.name "c", .name "v"]] (.name "$formalsw.unpack")] ++ rowStatements

theorem rowElement_result (env : HeapCalls.Env) (heap : Mutable.Heap) (p x left : Int)
    (getP : env "c" = some (number p)) (getX : env "v" = some (number x))
    (getLeft : env "prev" = some (number left)) :
    Evaluates program env rowElement heap (number (min p (left + x))) heap := by
  apply Evaluates.builtin (.cons (Evaluates.lookup getP)
    (.cons (Evaluates.binary (Evaluates.lookup getLeft) (Evaluates.lookup getX) rfl) .nil))
  by_cases smaller : left + x < p
  · simp [HeapCalls.primitive, Calls.positionalMinimum, Calls.minimumFrom, scalarCompare,
      evalCmpOp, HeapCalls.scalarResult, List.mapM, List.mapM.loop, smaller, Int.min_eq_right (show left + x ≤ p by omega)]
  · simp [HeapCalls.primitive, Calls.positionalMinimum, Calls.minimumFrom, scalarCompare,
      evalCmpOp, HeapCalls.scalarResult, List.mapM, List.mapM.loop, smaller, Int.min_eq_left (show p ≤ left + x by omega)]

theorem zip_read (base scratch : Mutable.Heap) (output previous row : List Int) (position : Nat) :
    zipItem [.ref (base.length + 1), .ref (base.length + 2)] position (rowHeap base output previous row scratch) =
      some (.ok (do
        let p ← previous[position]?
        let x ← row[position]?
        pure [number p, number x]), rowHeap base output previous row scratch) := by
  cases hp : previous[position]? <;> cases hx : row[position]? <;>
    simp [zipItem, zipFields, sequenceValue, Mutable.sequence, rowHeap, encode,
      List.append_assoc, hp, hx, Except.map]

theorem rowLoop_result (base scratch : Mutable.Heap) (output previous row : List Int)
    (position : Nat) (left : Int) (env : HeapCalls.Env)
    (same : previous.length = row.length)
    (getOut : env "out" = some (.ref base.length)) (getLeft : env "prev" = some (number left)) :
    ∃ finalScratch, BlockReturns program env
      [.zipStepLoop "$formalsw.unpack" [.ref (base.length + 1), .ref (base.length + 2)] position rowLoopBody [],
       .return (.name "out")]
      (rowHeap base output previous row scratch) (.ref base.length)
      (rowHeap base (output ++ relaxTail left (previous.drop position) (row.drop position)) previous row finalScratch) := by
  let heap := rowHeap base output previous row scratch
  by_cases active : position < previous.length
  · have inRow : position < row.length := by omega
    let p := previous[position]
    let x := row[position]
    let value := min p (left + x)
    let fields := [number p, number x]
    let nextScratch := scratch ++ [.tuple fields]
    let afterTuple := rowHeap base output previous row nextScratch
    let tupleEnv := setLocal env "$formalsw.unpack" (.ref heap.length)
    let unpacked := assignNames tupleEnv ["c", "v"] fields
    let withCur := setLocal unpacked "cur" (number value)
    let nextEnv := setLocal withCur "prev" (number value)
    have fetched : zipItem [.ref (base.length + 1), .ref (base.length + 2)] position heap =
        some (.ok (some fields), heap) := by
      simpa [heap, p, x, fields, List.getElem?_eq_getElem active, List.getElem?_eq_getElem inRow] using
        zip_read base scratch output previous row position
    have allocated : Mutable.allocateTuple fields heap = some (.ok (.ref heap.length), afterTuple) := by
      simp [Mutable.allocateTuple, fields, heap, afterTuple, nextScratch, rowHeap, List.append_assoc, Except.map]
    have tupleFound : Mutable.sequence (.ref heap.length) afterTuple = some (.ok fields, afterTuple) := by
      have equal : afterTuple = heap ++ [.tuple fields] := by simp [afterTuple, heap, nextScratch, rowHeap, List.append_assoc]
      simp [equal, Mutable.sequence]
    have appended : Evaluates program withCur (.call (.attribute (.name "out") "append") [.name "cur"])
        afterTuple (.scalar .none) (rowHeap base (output ++ [value]) previous row nextScratch) := by
      have result := Evaluates.append (globals := []) (module := program)
        (Evaluates.lookup (show withCur "out" = some (.ref base.length) by
          simpa [withCur, unpacked, tupleEnv, assignNames, fields, setLocal] using getOut))
        (rowHeap_output base nextScratch output previous row)
        (Evaluates.lookup (show withCur "cur" = some (number value) by simp [withCur, setLocal]))
        (rowHeap_output base nextScratch output previous row)
      have write : (rowHeap base output previous row nextScratch).set base.length
          (.list (encode output ++ [number value])) = rowHeap base (output ++ [value]) previous row nextScratch := by
        simpa [encode, number] using rowHeap_append base nextScratch output previous row value
      simpa only [write] using result
    obtain ⟨finalScratch, continued⟩ := rowLoop_result base nextScratch (output ++ [value]) previous row (position + 1)
      value nextEnv same
      (by simpa [nextEnv, withCur, unpacked, tupleEnv, assignNames, fields, setLocal] using getOut)
      (by simp [nextEnv, setLocal])
    have next : relaxTail left (previous.drop position) (row.drop position) =
        value :: relaxTail value (previous.drop (position + 1)) (row.drop (position + 1)) := by
      rw [List.drop_eq_getElem_cons active, List.drop_eq_getElem_cons inRow]
      rfl
    refine ⟨finalScratch, ?_⟩
    apply BlockReturns.zip_step fetched allocated
    apply BlockReturns.unpack rfl (Evaluates.lookup rfl) tupleFound rfl
    apply BlockReturns.assign (value := number value)
      (rowElement_result unpacked afterTuple p x left rfl rfl
        (by simpa [unpacked, tupleEnv, assignNames, fields, setLocal] using getLeft))
    apply BlockReturns.discard appended
    apply BlockReturns.assign (value := number value)
      (Evaluates.lookup (show withCur "cur" = some (number value) by simp [withCur, setLocal]))
    simpa [next, rowLoopBody, rowStatements, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt, List.append_assoc] using continued
  · have gone : previous.drop position = [] := List.drop_eq_nil_iff.mpr (by omega)
    have exhausted : zipItem [.ref (base.length + 1), .ref (base.length + 2)] position heap = some (.ok none, heap) := by
      rw [zip_read]
      simp [List.getElem?_eq_none (by omega : previous.length ≤ position)]
      rfl
    refine ⟨scratch, ?_⟩
    simp only [gone, relaxTail, List.append_nil]
    exact BlockReturns.zip_done exhausted (BlockReturns.return_value (Evaluates.lookup getOut))
termination_by previous.length - position
decreasing_by omega

end data.«project-euler-statements».data.py.project_euler_statements.p82
