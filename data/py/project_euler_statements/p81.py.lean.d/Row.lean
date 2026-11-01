import data.«project-euler-statements».data.py.project_euler_statements.«p81.py.lean.d».RowLoop

namespace data.«project-euler-statements».data.py.project_euler_statements.p81
open FormalSW.PyAst HeapCalls ProjectEulerStatements.P81
open ProjectEulerSolutions.RectangularMatrixCalls
set_option Elab.async false

abbrev rowGuard : Expr := .boolOp .or [.unaryOp .not (.name "prev"), .unaryOp .not (.name "row")]
abbrev rowSources : List Expr :=
  [.subscript (.name "prev") (.slice (some (.constant (.int 1))) none none),
   .subscript (.name "row") (.slice (some (.constant (.int 1))) none none)]

theorem rowGuard_result (heap : Mutable.Heap) (env : HeapCalls.Env) (prevAddress rowAddress : Nat)
    (previous row : List Int)
    (getPrevious : heap[prevAddress]? = some (.list (encode previous)))
    (getRow : heap[rowAddress]? = some (.list (encode row)))
    (localPrev : env "prev" = some (.ref prevAddress)) (localRow : env "row" = some (.ref rowAddress)) :
    Evaluates program env rowGuard heap (.scalar (.bool (decide (previous = [] ∨ row = [])))) heap := by
  have testedPrev : Evaluates program env (.unaryOp .not (.name "prev")) heap
      (.scalar (.bool (decide (previous = [])))) heap :=
    Evaluates.unary (Evaluates.lookup localPrev)
      (by simp [HeapCalls.unary, Mutable.truth, getPrevious, encode]; cases previous <;> rfl)
  have testedRow : Evaluates program env (.unaryOp .not (.name "row")) heap
      (.scalar (.bool (decide (row = [])))) heap :=
    Evaluates.unary (Evaluates.lookup localRow)
      (by simp [HeapCalls.unary, Mutable.truth, getRow, encode]; cases row <;> rfl)
  by_cases empty : previous = []
  · simp only [empty, true_or, decide_true] at testedPrev ⊢
    exact Evaluates.boolean_stop testedPrev rfl rfl
  · simp only [empty, false_or, decide_false] at testedPrev ⊢
    exact Evaluates.boolean_next testedPrev rfl rfl (Evaluates.boolean_last testedRow rfl)

theorem tails_result (heap : Mutable.Heap) (env : HeapCalls.Env) (prevAddress rowAddress : Nat)
    (previous row output : List Int)
    (getPrevious : heap[prevAddress]? = some (.list (encode previous)))
    (getRow : heap[rowAddress]? = some (.list (encode row)))
    (localPrev : env "prev" = some (.ref prevAddress)) (localRow : env "row" = some (.ref rowAddress)) :
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

theorem row_step.result (heap : Mutable.Heap) (prevAddress rowAddress : Nat) (previous row : List Int)
    (getPrevious : heap[prevAddress]? = some (.list (encode previous)))
    (getRow : heap[rowAddress]? = some (.list (encode row))) (same : previous.length = row.length) :
    ∃ extra address, ReturnsValue program "row_step" [.ref prevAddress, .ref rowAddress] heap (.ref address) (heap ++ extra) ∧
      (heap ++ extra)[address]? = some (.list (encode (rowStep previous row))) := by
  let args : List Arg :=
    [⟨"prev", some (.subscript (.name "list") (.name "int")), none⟩,
     ⟨"row", some (.subscript (.name "list") (.name "int")), none⟩]
  let entry := argumentEnv args [.ref prevAddress, .ref rowAddress]
  have guard := rowGuard_result heap entry prevAddress rowAddress previous row getPrevious getRow rfl rfl
  cases previous with
  | nil =>
      refine ⟨[.list []], heap.length, ?_, ?_⟩
      · apply BlockReturns.function rfl rfl
        apply BlockReturns.branch (flag := true) (by simpa only [true_or, decide_true] using guard) rfl
        exact BlockReturns.return_value (Evaluates.list .nil)
      · cases row <;> simp [rowStep, encode]
  | cons p ps =>
      cases row with
      | nil => simp at same
      | cons x xs =>
          let first := x + p
          let withFirst := setLocal entry "first" (number first)
          let withOutput := setLocal withFirst "out" (.ref heap.length)
          let ready := setLocal withOutput "left" (number first)
          have firstValue : Evaluates program entry (.binOp (.subscript (.name "row") (.constant (.int 0))) .add
              (.subscript (.name "prev") (.constant (.int 0)))) heap (number first) heap := by
            apply Evaluates.binary (av := number x) (bv := number p) (middle := heap) (afterRight := heap)
            · apply Evaluates.subscript (by intros a b c impossible; cases impossible) (Evaluates.lookup rfl) Evaluates.constant
              simp [Mutable.getItem, Mutable.index, getRow, encode, Except.map, number]
            · apply Evaluates.subscript (by intros a b c impossible; cases impossible) (Evaluates.lookup rfl) Evaluates.constant
              simp [Mutable.getItem, Mutable.index, getPrevious, encode, Except.map, number]
            · rfl
          have slices := tails_result heap ready prevAddress rowAddress (p :: ps) (x :: xs) [first]
            getPrevious getRow rfl rfl
          have captured : zipSources [.ref (heap.length + 1), .ref (heap.length + 2)] (rowHeap heap [first] ps xs []) =
              some (.ok [.ref (heap.length + 1), .ref (heap.length + 2)], rowHeap heap [first] ps xs []) := by
            simp [zipSources, List.mapM, List.mapM.loop, Mutable.sequence, rowHeap, sequenceSource, Except.map]
          obtain ⟨scratch, loop⟩ := rowLoop_result heap [] [first] ps xs 0 first ready (by simpa using same) rfl rfl
          refine ⟨[.list (encode (rowStep (p :: ps) (x :: xs))), .list (encode ps), .list (encode xs)] ++ scratch,
            heap.length, ?_, ?_⟩
          · apply BlockReturns.function rfl rfl
            apply BlockReturns.branch (flag := false) (by simpa using guard) rfl
            apply BlockReturns.assign firstValue
            apply BlockReturns.assign (value := .ref heap.length) (Evaluates.list (.cons (Evaluates.lookup rfl) .nil))
            apply BlockReturns.assign (value := number first) (Evaluates.lookup rfl)
            apply BlockReturns.for_zip slices captured
            simpa [comprehensionTargetName, comprehensionTargetBody, rowLoopBody, rowHeap, rowStep, first,
              List.append_assoc] using loop
          · simp

end data.«project-euler-statements».data.py.project_euler_statements.p81
