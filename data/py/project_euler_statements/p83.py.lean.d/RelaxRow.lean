import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».RelaxCell
import ProjectEulerSolutions.Lib.AllocatingIntegerRangeCollection

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.RectangularMatrixCalls (MatrixRows)
open ProjectEulerSolutions.TriangleBufferCalls
open ProjectEulerSolutions.AllocatingIntegerRangeCollection (state)
set_option Elab.async false

abbrev relaxedRowExpression : Expr := .listComp relaxedCellExpression [("c", .call (.name "range") [.name "cols"], [])]
def relaxedRow (matrix distances : List (List Int)) (row : Nat) : List Int :=
  (List.range (matrix.headD []).length).map (fun (col : Nat) => ProjectEulerSolutions.GridRelaxation.cell matrix distances row col)

theorem relaxed_row_allocation (heap : Mutable.Heap) (env : HeapCalls.Env) (matrixAddress distanceAddress row : Nat)
    (matrix distances : MatrixRows)
    (matrixFound : heap[matrixAddress]? = some (.list (matrix.map (fun entry => .ref entry.1))))
    (matrixReads : ∀ entry ∈ matrix, heap[entry.1]? = some (.list (encode entry.2)))
    (distanceFound : heap[distanceAddress]? = some (.list (distances.map (fun entry => .ref entry.1))))
    (distanceReads : ∀ entry ∈ distances, heap[entry.1]? = some (.list (encode entry.2)))
    (localMatrix : env "matrix" = some (.ref matrixAddress)) (localDistances : env "dist" = some (.ref distanceAddress))
    (localRow : env "r" = some (number row)) (localHeight : env "rows" = some (number matrix.length))
    (localWidth : env "cols" = some (number ((matrix.map Prod.snd).headD []).length)) :
    ∃ extra, Evaluates program env relaxedRowExpression heap (.ref heap.length)
      (working heap (relaxedRow (matrix.map Prod.snd) (distances.map Prod.snd) row) ++ extra) := by
  apply ProjectEulerSolutions.AllocatingIntegerRangeCollection.collect
    (values := relaxedRow (matrix.map Prod.snd) (distances.map Prod.snd) row)
    (evaluated := .cons (Evaluates.lookup localWidth) .nil) (bounds := by simp [relaxedRow]; rfl)
  intro collected objects index inside
  have value : (relaxedRow (matrix.map Prod.snd) (distances.map Prod.snd) row)[index] =
      ProjectEulerSolutions.GridRelaxation.cell (matrix.map Prod.snd) (distances.map Prod.snd) row index := by
    simp only [relaxedRow, List.getElem_map, List.getElem_range]
  rw [value]
  apply relaxed_cell (state heap collected objects) _ matrixAddress distanceAddress matrix distances row index
    (ProjectEulerSolutions.AllocatingIntegerRangeCollection.prefix_found heap objects collected matrixAddress _ matrixFound)
    (fun entry member => ProjectEulerSolutions.AllocatingIntegerRangeCollection.prefix_found heap objects collected entry.1 _ (matrixReads entry member))
    (ProjectEulerSolutions.AllocatingIntegerRangeCollection.prefix_found heap objects collected distanceAddress _ distanceFound)
    (fun entry member => ProjectEulerSolutions.AllocatingIntegerRangeCollection.prefix_found heap objects collected entry.1 _ (distanceReads entry member))
    (by simpa [setLocal, comprehensionEnv] using localMatrix)
    (by simpa [setLocal, comprehensionEnv] using localDistances)
    (by simpa [setLocal, comprehensionEnv] using localRow) rfl
    (by simpa [setLocal, comprehensionEnv] using localHeight)
    (by simpa [setLocal, comprehensionEnv] using localWidth)

end data.«project-euler-statements».data.py.project_euler_statements.p83
