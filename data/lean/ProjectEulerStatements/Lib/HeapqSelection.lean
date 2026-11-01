import ProjectEulerStatements.Lib.MinHeap
import lang.py.FormalSW.HeapqContents

/-! Relate a concrete successful heap pop to the greedy topological-order choice.
The caller must establish heap order and eligible contents; the concrete pop
theorems then supply the returned value and the exact remaining heap contents. -/
namespace ProjectEulerStatements.MinHeap
open FormalSW.PyAst
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

theorem heappop_selects_choose (encode : α → Mutable.Value)
    (nodes : List α) (edges : List (α × α)) (head : α) (rest : List α)
    (heap after : Mutable.Heap) (address : Nat) (returned : Mutable.Value)
    (contents : (head :: rest).Perm (TopologicalOrder.eligible nodes edges))
    (ordered : Ordered (head :: rest))
    (found : heap[address]? = some (.list ((head :: rest).map encode)))
    (finished : Heapq.heappop [.ref address] heap = some (.ok returned, after)) :
    TopologicalOrder.choose nodes edges = some head ∧ returned = encode head ∧
      Heapq.Reorders heap address (rest.map encode) after := by
  exact ⟨head_eq_choose nodes edges head rest contents ordered,
    Heapq.heappop_returns_root heap after address (encode head) returned (rest.map encode)
      found finished,
    Heapq.heappop_reorders heap after address (encode head) (rest.map encode) (.ok returned)
      found finished⟩

end ProjectEulerStatements.MinHeap
