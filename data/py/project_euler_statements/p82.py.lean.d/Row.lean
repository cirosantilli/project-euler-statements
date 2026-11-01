import data.«project-euler-statements».data.py.project_euler_statements.«p82.py.lean.d».RowLoop

namespace data.«project-euler-statements».data.py.project_euler_statements.p82
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P82
open ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

abbrev rowGuard : Expr := .boolOp .or
  [.compare (.builtinCall .len [.name "cost"]) [(.notEq, .builtinCall .len [.name "col"])],
   .unaryOp .not (.name "cost")]
abbrev rowSources : List Expr :=
  [.subscript (.name "cost") (.slice (some (.constant (.int 1))) none none),
   .subscript (.name "col") (.slice (some (.constant (.int 1))) none none)]

theorem rowGuard_result (heap : Mutable.Heap) (env : HeapCalls.Env) (prevAddress rowAddress : Nat)
    (previous row : List Int)
    (getPrevious : heap[prevAddress]? = some (.list (encode previous)))
    (getRow : heap[rowAddress]? = some (.list (encode row)))
    (same : previous.length = row.length)
    (localPrev : env "cost" = some (.ref prevAddress)) (localRow : env "col" = some (.ref rowAddress)) :
    Evaluates program env rowGuard heap (.scalar (.bool (decide (previous = [])))) heap := by
  have lengthPrevious : Evaluates program env (.builtinCall .len [.name "cost"]) heap (number previous.length) heap :=
    Evaluates.builtin (.cons (Evaluates.lookup localPrev) .nil) (by simp [HeapCalls.primitive, Mutable.length, getPrevious, encode])
  have lengthRow : Evaluates program env (.builtinCall .len [.name "col"]) heap (number row.length) heap :=
    Evaluates.builtin (.cons (Evaluates.lookup localRow) .nil) (by simp [HeapCalls.primitive, Mutable.length, getRow, encode])
  have sizes : Evaluates program env (.compare (.builtinCall .len [.name "cost"]) [(.notEq, .builtinCall .len [.name "col"])])
      heap (.scalar (.bool false)) heap :=
    Evaluates.compare lengthPrevious lengthRow (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, same])
  have empty : Evaluates program env (.unaryOp .not (.name "cost")) heap (.scalar (.bool (decide (previous = [])))) heap :=
    Evaluates.unary (Evaluates.lookup localPrev)
      (by simp [HeapCalls.unary, Mutable.truth, getPrevious, encode]; cases previous <;> rfl)
  exact Evaluates.boolean_next sizes rfl rfl (Evaluates.boolean_last empty rfl)

theorem tails_result (heap : Mutable.Heap) (env : HeapCalls.Env) (prevAddress rowAddress : Nat)
    (previous row output : List Int)
    (getPrevious : heap[prevAddress]? = some (.list (encode previous)))
    (getRow : heap[rowAddress]? = some (.list (encode row)))
    (localPrev : env "cost" = some (.ref prevAddress)) (localRow : env "col" = some (.ref rowAddress)) :
    Evaluates.Arguments program env rowSources (heap ++ [.list (encode output)])
      [.ref (heap.length + 1), .ref (heap.length + 2)]
      (rowHeap heap output previous.tail row.tail []) := by
  let withOutput := heap ++ [.list (encode output)]
  let withPrevious := withOutput ++ [.list (encode previous.tail)]
  have prevRead : withOutput[prevAddress]? = some (.list (encode previous)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp getPrevious).1]
    exact getPrevious
  have rowRead : withPrevious[rowAddress]? = some (.list (encode row)) := by
    simp only [withPrevious, withOutput, List.append_assoc]
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp getRow).1]
    exact getRow
  apply Evaluates.Arguments.cons (middle := withPrevious)
  · apply Evaluates.slice (.cons (Evaluates.lookup localPrev)
      (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
    simpa [withOutput, withPrevious, encode, List.drop_one] using
      Mutable.getSlice_list_suffix withOutput prevAddress (encode previous) 1 prevRead
  · apply Evaluates.Arguments.cons
    · apply Evaluates.slice (.cons (Evaluates.lookup localRow)
        (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
      simpa [withPrevious, withOutput, rowHeap, encode, List.drop_one, List.append_assoc] using
        Mutable.getSlice_list_suffix withPrevious rowAddress (encode row) 1 rowRead
    · simpa [rowHeap, encode, List.map_tail, List.append_assoc] using
        (Evaluates.Arguments.nil (module := program) (env := env)
          (heap := rowHeap heap output previous.tail row.tail []))


theorem relax_down.result (heap : Mutable.Heap) (prevAddress rowAddress : Nat) (previous row : List Int)
    (getPrevious : heap[prevAddress]? = some (.list (encode previous)))
    (getRow : heap[rowAddress]? = some (.list (encode row))) (same : previous.length = row.length) :
    ∃ extra address, ReturnsValue program "relax_down" [.ref prevAddress, .ref rowAddress] heap (.ref address) (heap ++ extra) ∧
      (heap ++ extra)[address]? = some (.list (encode (relaxDown previous row))) := by
  let args : List Arg :=
    [⟨"cost", some (.subscript (.name "list") (.name "int")), none⟩,
     ⟨"col", some (.subscript (.name "list") (.name "int")), none⟩]
  let entry := argumentEnv args [.ref prevAddress, .ref rowAddress]
  have guard := rowGuard_result heap entry prevAddress rowAddress previous row getPrevious getRow same rfl rfl
  cases previous with
  | nil =>
      refine ⟨[.list []], heap.length, ?_, ?_⟩
      · apply BlockReturns.function rfl rfl
        apply BlockReturns.branch (flag := true) guard rfl
        exact BlockReturns.return_value (Evaluates.list .nil)
      · simp [relaxDown, same, encode]
  | cons p ps =>
      cases row with
      | nil => simp at same
      | cons x xs =>
          let withOutput := setLocal entry "out" (.ref heap.length)
          let ready := setLocal withOutput "prev" (number p)
          have firstValue : Evaluates program entry (.subscript (.name "cost") (.constant (.int 0))) heap (number p) heap := by
            apply Evaluates.subscript (by intros a b c impossible; cases impossible) (Evaluates.lookup rfl) Evaluates.constant
            simp [Mutable.getItem, Mutable.index, getPrevious, encode, Except.map, number]
          have previousKept : (heap ++ [.list (encode [p])])[prevAddress]? = some (.list (encode (p :: ps))) := by
            rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp getPrevious).1]
            exact getPrevious
          have copied : Evaluates program withOutput (.subscript (.name "cost") (.constant (.int 0)))
              (heap ++ [.list (encode [p])]) (number p) (heap ++ [.list (encode [p])]) := by
            apply Evaluates.subscript (by intros a b c impossible; cases impossible) (Evaluates.lookup rfl) Evaluates.constant
            simp only [encode, List.map_cons, List.map_nil] at previousKept
            simp [Mutable.getItem, Mutable.index, previousKept, encode, Except.map, number]
          have slices := tails_result heap ready prevAddress rowAddress (p :: ps) (x :: xs) [p]
            getPrevious getRow rfl rfl
          have captured : zipSources [.ref (heap.length + 1), .ref (heap.length + 2)] (rowHeap heap [p] ps xs []) =
              some (.ok [.ref (heap.length + 1), .ref (heap.length + 2)], rowHeap heap [p] ps xs []) := by
            simp [zipSources, List.mapM, List.mapM.loop, Mutable.sequence, rowHeap, sequenceSource, Except.map]
          obtain ⟨scratch, loop⟩ := rowLoop_result heap [] [p] ps xs 0 p ready (by simpa using same) rfl rfl
          refine ⟨[.list (encode (relaxDown (p :: ps) (x :: xs))), .list (encode ps), .list (encode xs)] ++ scratch,
            heap.length, ?_, ?_⟩
          · apply BlockReturns.function rfl rfl
            apply BlockReturns.branch (flag := false) guard rfl
            apply BlockReturns.assign (value := .ref heap.length) (Evaluates.list (.cons firstValue .nil))
            apply BlockReturns.assign copied
            apply BlockReturns.for_zip slices captured
            simpa [comprehensionTargetName, comprehensionTargetBody, rowLoopBody, rowHeap, relaxDown, same,
              List.append_assoc] using loop
          · simp

end data.«project-euler-statements».data.py.project_euler_statements.p82
