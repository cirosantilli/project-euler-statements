import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».RelaxRow
import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».Initial
import ProjectEulerSolutions.Lib.AllocatingMatrixRangeCollection

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.RectangularMatrixCalls (MatrixRows arguments)
open ProjectEulerSolutions.TriangleBufferCalls
open ProjectEulerSolutions.AllocatingMatrixRangeCollection (state prefix_found)
open ProjectEulerStatements.P83 (relaxStep)
set_option Elab.async false

abbrev relaxedMatrixExpression : Expr := .listComp relaxedRowExpression [("r", .call (.name "range") [.name "rows"], [])]
abbrev relaxArgs : List Arg := arguments ++
  [⟨"dist", some (.subscript (.name "list") (.subscript (.name "list") (.name "int"))), none⟩]

theorem relaxed_matrix_allocation (heap : Mutable.Heap) (env : HeapCalls.Env) (matrixAddress distanceAddress : Nat)
    (matrix distances : MatrixRows)
    (matrixFound : heap[matrixAddress]? = some (.list (matrix.map (fun row => .ref row.1))))
    (matrixReads : ∀ row ∈ matrix, heap[row.1]? = some (.list (encode row.2)))
    (distanceFound : heap[distanceAddress]? = some (.list (distances.map (fun row => .ref row.1))))
    (distanceReads : ∀ row ∈ distances, heap[row.1]? = some (.list (encode row.2)))
    (localMatrix : env "matrix" = some (.ref matrixAddress)) (localDistances : env "dist" = some (.ref distanceAddress))
    (localHeight : env "rows" = some (number matrix.length))
    (localWidth : env "cols" = some (number ((matrix.map Prod.snd).headD []).length)) :
    ∃ (extra : Mutable.Heap) (result : MatrixRows),
      Evaluates program env relaxedMatrixExpression heap (.ref heap.length) (state heap result extra) ∧
      result.map Prod.snd = relaxStep (matrix.map Prod.snd) (distances.map Prod.snd) ∧
      (∀ row ∈ result, (state heap result extra)[row.1]? = some (.list (encode row.2))) := by
  rw [ProjectEulerSolutions.GridRelaxation.relaxStep_eq]
  simp only [List.length_map]
  apply ProjectEulerSolutions.AllocatingMatrixRangeCollection.collect
    (values := relaxedRow (matrix.map Prod.snd) (distances.map Prod.snd))
    (evaluated := .cons (Evaluates.lookup localHeight) .nil) (bounds := rfl)
  intro collected objects index inside
  exact relaxed_row_allocation (state heap collected objects) _ matrixAddress distanceAddress index matrix distances
    (prefix_found heap objects collected matrixAddress _ matrixFound)
    (fun row member => prefix_found heap objects collected row.1 _ (matrixReads row member))
    (prefix_found heap objects collected distanceAddress _ distanceFound)
    (fun row member => prefix_found heap objects collected row.1 _ (distanceReads row member))
    (by simpa [setLocal, comprehensionEnv] using localMatrix)
    (by simpa [setLocal, comprehensionEnv] using localDistances) rfl
    (by simpa [setLocal, comprehensionEnv] using localHeight)
    (by simpa [setLocal, comprehensionEnv] using localWidth)

theorem relax_step.result (heap : Mutable.Heap) (matrixAddress distanceAddress : Nat) (matrix distances : MatrixRows)
    (matrixFound : heap[matrixAddress]? = some (.list (matrix.map (fun row => .ref row.1))))
    (matrixReads : ∀ row ∈ matrix, heap[row.1]? = some (.list (encode row.2)))
    (distanceFound : heap[distanceAddress]? = some (.list (distances.map (fun row => .ref row.1))))
    (distanceReads : ∀ row ∈ distances, heap[row.1]? = some (.list (encode row.2))) :
    ∃ (extra : Mutable.Heap) (resultAddress : Nat) (result : MatrixRows),
      ReturnsValue program "relax_step" [.ref matrixAddress, .ref distanceAddress] heap (.ref resultAddress) (heap ++ extra) ∧
      (heap ++ extra)[resultAddress]? = some (.list (result.map (fun row => .ref row.1))) ∧
      (∀ row ∈ result, (heap ++ extra)[row.1]? = some (.list (encode row.2))) ∧
      result.map Prod.snd = relaxStep (matrix.map Prod.snd) (distances.map Prod.snd) := by
  let entry := argumentEnv relaxArgs [.ref matrixAddress, .ref distanceAddress]
  let base := heap ++ [dimensionObject matrix]
  let ready := assignNames entry ["rows", "cols"] [number matrix.length, number ((matrix.map Prod.snd).headD []).length]
  have kept (address : Nat) (object : Mutable.Object) (read : heap[address]? = some object) : base[address]? = some object := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
    exact read
  have dimensions : Evaluates program entry (.call (.name "dims") [.name "matrix"]) heap (.ref heap.length) base :=
    Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (dims.result heap matrixAddress matrix matrixFound matrixReads)
  obtain ⟨extra, result, allocated, data, reads⟩ := relaxed_matrix_allocation base ready matrixAddress distanceAddress matrix distances
    (kept _ _ matrixFound) (fun row member => kept _ _ (matrixReads row member))
    (kept _ _ distanceFound) (fun row member => kept _ _ (distanceReads row member)) rfl rfl rfl rfl
  refine ⟨[dimensionObject matrix, .list (result.map (fun row => .ref row.1))] ++ extra,
    heap.length + 1, result, ?_, ?_, ?_, data⟩
  · apply BlockReturns.function (args := relaxArgs) rfl rfl
    apply BlockReturns.unpack (afterUnpack := base) (names := ["rows", "cols"]) rfl dimensions
      (items := [number matrix.length, number ((matrix.map Prod.snd).headD []).length])
      (by simp [Mutable.sequence, base, dimensionObject]) rfl
    simpa only [state, base, List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] using
      BlockReturns.return_value allocated
  · simp
  · simpa only [state, base, List.append_assoc, List.singleton_append] using reads

end data.«project-euler-statements».data.py.project_euler_statements.p83
