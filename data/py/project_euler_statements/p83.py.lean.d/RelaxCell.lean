import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».NeighborCosts
import ProjectEulerSolutions.Lib.IntegerListMinimumCalls
import ProjectEulerSolutions.Lib.GridRelaxation
import lang.py.FormalSW.SequenceArithmeticRelocation

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls
open ProjectEulerSolutions.RectangularMatrixCalls (MatrixRows)
open ProjectEulerSolutions.TriangleBufferCalls
open ProjectEulerSolutions.IntegerListMinimumCalls
open ProjectEulerStatements.P83 (getD2 neighbors)
set_option Elab.async false

abbrev currentDistance : Expr := .call (.name "get_d2") [.name "dist", .name "r", .name "c"]
abbrev currentCost : Expr := .call (.name "get_d2") [.name "matrix", .name "r", .name "c"]
abbrev candidatesWithCurrent : Expr := .binOp neighborCostsExpression .add (.list [currentDistance])
abbrev relaxedCellExpression : Expr := .builtinCall .min
  [currentDistance, .binOp currentCost .add (.builtinCall .min [candidatesWithCurrent])]

theorem relaxed_cell (heap : Mutable.Heap) (env : HeapCalls.Env) (matrixAddress distanceAddress : Nat)
    (matrix distances : MatrixRows) (r c : Int)
    (matrixFound : heap[matrixAddress]? = some (.list (matrix.map (fun row => .ref row.1))))
    (matrixReads : ∀ row ∈ matrix, heap[row.1]? = some (.list (encode row.2)))
    (distanceFound : heap[distanceAddress]? = some (.list (distances.map (fun row => .ref row.1))))
    (distanceReads : ∀ row ∈ distances, heap[row.1]? = some (.list (encode row.2)))
    (localMatrix : env "matrix" = some (.ref matrixAddress)) (localDistances : env "dist" = some (.ref distanceAddress))
    (localRow : env "r" = some (number r)) (localColumn : env "c" = some (number c))
    (localHeight : env "rows" = some (number matrix.length))
    (localWidth : env "cols" = some (number ((matrix.map Prod.snd).headD []).length)) :
    ∃ extra, Evaluates program env relaxedCellExpression heap
      (number (ProjectEulerSolutions.GridRelaxation.cell (matrix.map Prod.snd) (distances.map Prod.snd) r c)) (heap ++ extra) := by
  let current := getD2 (distances.map Prod.snd) r c
  let value := getD2 (matrix.map Prod.snd) r c
  let costs := (neighbors r c matrix.length ((matrix.map Prod.snd).headD []).length).map
    (fun pair => getD2 (distances.map Prod.snd) pair.1 pair.2)
  have current_read (extra : Mutable.Heap) : Evaluates program env currentDistance (heap ++ extra) (number current) (heap ++ extra) := by
    apply Evaluates.call (.cons (Evaluates.lookup localDistances)
      (.cons (Evaluates.lookup localRow) (.cons (Evaluates.lookup localColumn) .nil)))
    apply get_d2.result
    · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp distanceFound).1]
      exact distanceFound
    · intro row member
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp (distanceReads row member)).1]
      exact distanceReads row member
  have current_call : Evaluates program env currentDistance heap (number current) heap := by
    simpa only [List.append_nil] using current_read []
  have value_call : Evaluates program env currentCost heap (number value) heap :=
    Evaluates.call (.cons (Evaluates.lookup localMatrix)
      (.cons (Evaluates.lookup localRow) (.cons (Evaluates.lookup localColumn) .nil)))
      (get_d2.result heap matrixAddress matrix r c matrixFound matrixReads)
  obtain ⟨allocated, costsAddress, costCall, costFound⟩ := neighbor_costs_allocation heap env distanceAddress matrix.length
    ((matrix.map Prod.snd).headD []).length distances r c distanceFound distanceReads
    localDistances localRow localColumn localHeight localWidth
  let middle := heap ++ allocated
  let withCurrent := middle ++ [.list (encode [current])]
  let finalHeap := withCurrent ++ [.list (encode (costs ++ [current]))]
  have singleton : Evaluates program env (.list [currentDistance]) middle (.ref middle.length) withCurrent :=
    Evaluates.list (.cons (current_read allocated) .nil)
  have existing : withCurrent[costsAddress]? = some (.list (encode costs)) := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp costFound).1]
    exact costFound
  have lastFound : withCurrent[middle.length]? = some (.list (encode [current])) := by simp [withCurrent]
  have concatenate : Mutable.binary .add (.ref costsAddress) (.ref middle.length) withCurrent =
      some (.ok (.ref withCurrent.length), finalHeap) := by
    rw [Mutable.Relocation.binary_add_lists_eval withCurrent costsAddress middle.length _ _ existing lastFound]
    simp [Mutable.allocate, finalHeap, encode, Except.map]
  have candidatesCall : Evaluates program env candidatesWithCurrent heap (.ref withCurrent.length) finalHeap :=
    Evaluates.binary costCall singleton concatenate
  have combinedFound : finalHeap[withCurrent.length]? = some (.list (encode (costs ++ [current]))) := by simp [finalHeap]
  have minimumCall := minimum_with_last program env candidatesWithCurrent heap finalHeap withCurrent.length
    costs current candidatesCall combinedFound
  have added : Evaluates program env (.binOp currentCost .add (.builtinCall .min [candidatesWithCurrent])) heap
      (number (value + costs.foldl min current)) finalHeap := Evaluates.binary value_call minimumCall rfl
  have answer := minimum_pair program env currentDistance _ heap heap finalHeap current (value + costs.foldl min current)
    current_call added
  refine ⟨allocated ++ [.list (encode [current]), .list (encode (costs ++ [current]))], ?_⟩
  simpa only [ProjectEulerSolutions.GridRelaxation.cell, List.length_map, List.foldl_map,
    current, value, costs, finalHeap, withCurrent, middle, List.append_assoc, List.singleton_append] using answer

end data.«project-euler-statements».data.py.project_euler_statements.p83
