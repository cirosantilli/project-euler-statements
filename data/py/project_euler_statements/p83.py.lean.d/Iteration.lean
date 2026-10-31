import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».Relaxation

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.RectangularMatrixCalls (MatrixRows)
open ProjectEulerSolutions.TriangleBufferCalls
open ProjectEulerStatements.P83 (relaxStep iterate)
set_option Elab.async false

abbrev iterationBody : List Stmt :=
  [.assign [.name "dist"] (.call (.name "relax_step") [.name "matrix", .name "dist"])]
def remainingIterations (matrix distances : List (List Int)) (cursor total : Nat) : List (List Int) :=
  (List.range' cursor (total - cursor)).foldl (fun current _ => relaxStep matrix current) distances

theorem iteration_loop (heap : Mutable.Heap) (env : HeapCalls.Env) (matrixAddress distanceAddress cursor total : Nat)
    (matrix distances : MatrixRows) (bounded : cursor ≤ total)
    (matrixFound : heap[matrixAddress]? = some (.list (matrix.map (fun row => .ref row.1))))
    (matrixReads : ∀ row ∈ matrix, heap[row.1]? = some (.list (encode row.2)))
    (distanceFound : heap[distanceAddress]? = some (.list (distances.map (fun row => .ref row.1))))
    (distanceReads : ∀ row ∈ distances, heap[row.1]? = some (.list (encode row.2)))
    (localMatrix : env "matrix" = some (.ref matrixAddress)) (localDistances : env "dist" = some (.ref distanceAddress)) :
    ∃ (extra : Mutable.Heap) (resultAddress : Nat) (result : MatrixRows),
      BlockReturns program env [.rangeStepLoop "_" cursor total 1 iterationBody [], .return (.name "dist")]
        heap (.ref resultAddress) (heap ++ extra) ∧
      (heap ++ extra)[resultAddress]? = some (.list (result.map (fun row => .ref row.1))) ∧
      (∀ row ∈ result, (heap ++ extra)[row.1]? = some (.list (encode row.2))) ∧
      result.map Prod.snd = remainingIterations (matrix.map Prod.snd) (distances.map Prod.snd) cursor total := by
  by_cases active : cursor < total
  · let entered := setLocal env "_" (number cursor)
    obtain ⟨allocated, nextAddress, nextRows, returned, found, reads, data⟩ :=
      relax_step.result heap matrixAddress distanceAddress matrix distances matrixFound matrixReads distanceFound distanceReads
    have called : Evaluates program entered (.call (.name "relax_step") [.name "matrix", .name "dist"])
        heap (.ref nextAddress) (heap ++ allocated) :=
      Evaluates.call (.cons (Evaluates.lookup (by simpa [entered, setLocal] using localMatrix))
        (.cons (Evaluates.lookup (by simpa [entered, setLocal] using localDistances)) .nil)) returned
    let ready := setLocal entered "dist" (.ref nextAddress)
    have kept (address : Nat) (object : Mutable.Object) (read : heap[address]? = some object) :
        (heap ++ allocated)[address]? = some object := by
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
      exact read
    obtain ⟨more, finalAddress, result, continued, finalFound, finalReads, finalData⟩ :=
      iteration_loop (heap ++ allocated) ready matrixAddress nextAddress (cursor + 1) total matrix nextRows (by omega)
        (kept _ _ matrixFound) (fun row member => kept _ _ (matrixReads row member)) found reads
        (by simpa [ready, entered, setLocal] using localMatrix) rfl
    refine ⟨allocated ++ more, finalAddress, result, ?_, ?_, ?_, ?_⟩
    · apply BlockReturns.range_step (by simp [Calls.rangeContinues]; omega)
      apply BlockReturns.assign called
      simpa only [iterationBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        Bool.false_or, Bool.false_eq_true, if_false, Int.natCast_add, Int.natCast_one, List.append_assoc] using continued
    · simpa only [List.append_assoc] using finalFound
    · simpa only [List.append_assoc] using finalReads
    · rw [finalData, data]
      unfold remainingIterations
      rw [show total - cursor = (total - (cursor + 1)) + 1 by omega, List.range'_succ, List.foldl_cons]
  · have done : cursor = total := by omega
    subst cursor
    refine ⟨[], distanceAddress, distances, ?_, ?_, ?_, ?_⟩
    · simp only [List.append_nil]
      exact BlockReturns.range_done (by simp [Calls.rangeContinues]) (BlockReturns.return_value (Evaluates.lookup localDistances))
    · simpa only [List.append_nil] using distanceFound
    · simpa only [List.append_nil] using distanceReads
    · simp [remainingIterations]
termination_by total - cursor
decreasing_by omega

theorem iterate.result (heap : Mutable.Heap) (matrixAddress distanceAddress : Nat) (matrix distances : MatrixRows)
    (matrixFound : heap[matrixAddress]? = some (.list (matrix.map (fun row => .ref row.1))))
    (matrixReads : ∀ row ∈ matrix, heap[row.1]? = some (.list (encode row.2)))
    (distanceFound : heap[distanceAddress]? = some (.list (distances.map (fun row => .ref row.1))))
    (distanceReads : ∀ row ∈ distances, heap[row.1]? = some (.list (encode row.2))) :
    ∃ (extra : Mutable.Heap) (resultAddress : Nat) (result : MatrixRows),
      ReturnsValue program "iterate" [.ref matrixAddress, .ref distanceAddress] heap (.ref resultAddress) (heap ++ extra) ∧
      (heap ++ extra)[resultAddress]? = some (.list (result.map (fun row => .ref row.1))) ∧
      (∀ row ∈ result, (heap ++ extra)[row.1]? = some (.list (encode row.2))) ∧
      result.map Prod.snd = iterate (matrix.map Prod.snd) (distances.map Prod.snd) := by
  let entry := argumentEnv relaxArgs [.ref matrixAddress, .ref distanceAddress]
  let base := heap ++ [dimensionObject matrix]
  let ready := assignNames entry ["rows", "cols"] [number matrix.length, number ((matrix.map Prod.snd).headD []).length]
  have kept (address : Nat) (object : Mutable.Object) (read : heap[address]? = some object) : base[address]? = some object := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
    exact read
  have dimensions : Evaluates program entry (.call (.name "dims") [.name "matrix"]) heap (.ref heap.length) base :=
    Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (dims.result heap matrixAddress matrix matrixFound matrixReads)
  have count : Evaluates program ready (.binOp (.name "rows") .mult (.name "cols")) base
      (number (matrix.length * ((matrix.map Prod.snd).headD []).length : Nat)) base :=
    Evaluates.binary (Evaluates.lookup rfl) (Evaluates.lookup rfl) (by simp [Mutable.binary, scalarBinary])
  obtain ⟨extra, resultAddress, result, loop, found, reads, data⟩ := iteration_loop base ready matrixAddress distanceAddress 0
    (matrix.length * ((matrix.map Prod.snd).headD []).length) matrix distances (by omega)
    (kept _ _ matrixFound) (fun row member => kept _ _ (matrixReads row member))
    (kept _ _ distanceFound) (fun row member => kept _ _ (distanceReads row member)) rfl rfl
  refine ⟨[dimensionObject matrix] ++ extra, resultAddress, result, ?_, ?_, ?_, ?_⟩
  · apply BlockReturns.function (args := relaxArgs) rfl rfl
    apply BlockReturns.unpack (afterUnpack := base) (names := ["rows", "cols"]) rfl dimensions
      (items := [number matrix.length, number ((matrix.map Prod.snd).headD []).length])
      (by simp [Mutable.sequence, base, dimensionObject]) rfl
    apply BlockReturns.for_range (.cons count .nil) rfl
    simpa only [base, List.append_assoc] using loop
  · simpa only [base, List.append_assoc] using found
  · simpa only [base, List.append_assoc] using reads
  · simpa only [remainingIterations, Nat.sub_zero, ← List.range_eq_range', iterate, ProjectEulerStatements.P83.dims, List.length_map] using data

end data.«project-euler-statements».data.py.project_euler_statements.p83
