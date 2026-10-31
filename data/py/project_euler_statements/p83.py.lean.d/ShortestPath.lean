import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».Execution
import ProjectEulerSolutions.Lib.GridShortestPaths

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.RectangularMatrixCalls (MatrixRows)
open ProjectEulerSolutions.TriangleBufferCalls (number encode)
open ProjectEulerSolutions.FiniteGridGraph (graph origin)
open ProjectEulerSolutions.GridShortestPaths (finish cost)
set_option Elab.async false

/-- The actual reference call returns the cost of a shortest grid walk and preserves caller objects. -/
theorem naive.minimum_result (heap : Mutable.Heap) (address : Nat) (rows : MatrixRows)
    (found : heap[address]? = some (.list (rows.map (fun row => .ref row.1))))
    (reads : ∀ row ∈ rows, heap[row.1]? = some (.list (encode row.2)))
    (shape : ∀ row ∈ rows.map Prod.snd, row.length = ((rows.map Prod.snd).headD []).length)
    (nonnegative : ∀ row ∈ rows.map Prod.snd, ∀ value ∈ row, 0 ≤ value)
    (rowsPositive : 0 < (rows.map Prod.snd).length)
    (colsPositive : 0 < ((rows.map Prod.snd).headD []).length) :
    ∃ shortest : (graph (rows.map Prod.snd).length ((rows.map Prod.snd).headD []).length).Walk
        (finish (rows.map Prod.snd) rowsPositive colsPositive) (origin rowsPositive colsPositive),
      (∃ extra, ReturnsValue program "naive" [.ref address] heap
        (number (shortest.support.map (cost (rows.map Prod.snd))).sum) (heap ++ extra)) ∧
      ∀ walk : (graph (rows.map Prod.snd).length ((rows.map Prod.snd).headD []).length).Walk
          (finish (rows.map Prod.snd) rowsPositive colsPositive) (origin rowsPositive colsPositive),
        (shortest.support.map (cost (rows.map Prod.snd))).sum ≤
          (walk.support.map (cost (rows.map Prod.snd))).sum := by
  obtain ⟨shortest, value, minimal⟩ := ProjectEulerSolutions.GridShortestPaths.naive_minimum
    (rows.map Prod.snd) shape nonnegative rowsPositive colsPositive
  refine ⟨shortest, ?_, minimal⟩
  rw [value]
  exact naive.result heap address rows found reads

end data.«project-euler-statements».data.py.project_euler_statements.p83
