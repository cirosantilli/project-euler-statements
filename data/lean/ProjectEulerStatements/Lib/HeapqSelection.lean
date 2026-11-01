import ProjectEulerStatements.Lib.MinHeap
import lang.py.FormalSW.HeapqTotal

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

/-- Total comparisons establish the concrete pop's execution as well as its selected vertex. -/
theorem heappop_greedy_succeeds (encode : α → Mutable.Value)
    (comparable : Heapq.TotalComparison (fun value => ∃ vertex, value = encode vertex))
    (nodes : List α) (edges : List (α × α)) (head : α) (rest : List α)
    (heap : Mutable.Heap) (address : Nat)
    (contents : (head :: rest).Perm (TopologicalOrder.eligible nodes edges))
    (ordered : Ordered (head :: rest))
    (found : heap[address]? = some (.list ((head :: rest).map encode))) :
    ∃ after, Heapq.heappop [.ref address] heap = some (.ok (encode head), after) ∧
      TopologicalOrder.choose nodes edges = some head ∧
      Heapq.Reorders heap address (rest.map encode) after := by
  have typed : ∀ value ∈ (head :: rest).map encode, ∃ vertex, value = encode vertex := by
    intro value member
    obtain ⟨vertex, _, rfl⟩ := List.mem_map.mp member
    exact ⟨vertex, rfl⟩
  obtain ⟨after, finished⟩ := Heapq.heappop_succeeds _ comparable heap address (encode head)
    (rest.map encode) typed found
  have selected := heappop_selects_choose encode nodes edges head rest heap after address
    (encode head) contents ordered found finished
  exact ⟨after, finished, selected.1, selected.2.2⟩

end ProjectEulerStatements.MinHeap
