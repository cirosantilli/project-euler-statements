import ProjectEulerStatements.Lib.TopologicalOrder
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup

/-! Incoming-edge counts and incremental readiness for finite precedence graphs.

Counts include every edge occurrence. Deduplicated graphs additionally permit one
decrement per successor, as used by a set-valued adjacency table. No order of
successor traversal is required. -/
namespace ProjectEulerStatements.TopologicalOrder
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

def indegree (vertex : α) (edges : List (α × α)) : Nat :=
  edges.countP (fun edge => decide (edge.2 = vertex))

def successors (vertex : α) (edges : List (α × α)) : List α :=
  (edges.filter (fun edge => decide (edge.1 = vertex))).map Prod.snd

theorem indegree_zero_iff (vertex : α) (edges : List (α × α)) :
    indegree vertex edges = 0 ↔ Ready vertex edges := by
  simp [indegree, Ready]

theorem mem_successors (source target : α) (edges : List (α × α)) :
    target ∈ successors source edges ↔ (source, target) ∈ edges := by
  simp only [successors, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨member, rfl⟩, rfl⟩
    exact member
  · intro member
    exact ⟨(source, target), ⟨member, rfl⟩, rfl⟩

theorem successors_nodup (vertex : α) (edges : List (α × α)) (unique : edges.Nodup) :
    (successors vertex edges).Nodup := by
  apply (List.nodup_map_iff_inj_on (unique.filter _)).mpr
  intro a ha b hb same
  have leftA := (List.mem_filter.mp ha).2
  have leftB := (List.mem_filter.mp hb).2
  apply Prod.ext
  · simpa using (of_decide_eq_true leftA).trans (of_decide_eq_true leftB).symm
  · exact same

/-- A new edge increments exactly its target's count; a repeated edge changes nothing. -/
theorem indegree_insert (source target vertex : α) (edges : List (α × α)) :
    indegree vertex (if (source, target) ∈ edges then edges else (source, target) :: edges) =
      indegree vertex edges + if (source, target) ∉ edges ∧ target = vertex then 1 else 0 := by
  by_cases present : (source, target) ∈ edges <;>
    by_cases same : target = vertex <;> simp_all [indegree]

/-- Removing a ready vertex removes precisely its outgoing contributions. -/
theorem indegree_remove_partition (source target : α) (edges : List (α × α))
    (ready : Ready source edges) :
    indegree target edges = indegree target (removeNode source edges) +
      (successors source edges).count target := by
  induction edges with
  | nil => simp [indegree, removeNode, successors]
  | cons edge rest ih =>
      have headReady := ready edge (by simp)
      have tailReady : Ready source rest := fun e member => ready e (by simp [member])
      have tail := ih tailReady
      by_cases outgoing : edge.1 = source <;> by_cases incoming : edge.2 = target <;>
        simp_all [indegree, removeNode, successors] <;> omega

/-- Integer updates match Python's subtraction, without truncated natural subtraction. -/
def decrement (counts : α → Int) (vertex : α) : α → Int :=
  fun target => counts target - if vertex = target then 1 else 0

def decrementAll (counts : α → Int) (neighbors : List α) : α → Int :=
  neighbors.foldl decrement counts

theorem decrementAll_apply (counts : α → Int) (neighbors : List α) (target : α) :
    decrementAll counts neighbors target = counts target - neighbors.count target := by
  induction neighbors generalizing counts with
  | nil => simp [decrementAll]
  | cons vertex rest ih =>
      change decrementAll (decrement counts vertex) rest target = _
      rw [ih]
      by_cases same : vertex = target
      · simp [decrement, same]
        omega
      · simp [decrement, same]

theorem decrementAll_perm (counts : α → Int) (first second : List α)
    (permutation : first.Perm second) :
    decrementAll counts first = decrementAll counts second := by
  funext target
  simp only [decrementAll_apply, permutation.count_eq]

theorem decrementAll_indegree (source : α) (edges : List (α × α)) (neighbors : List α)
    (ready : Ready source edges) (contents : neighbors.Perm (successors source edges)) :
    decrementAll (fun vertex => (indegree vertex edges : Int)) neighbors =
      fun vertex => (indegree vertex (removeNode source edges) : Int) := by
  funext target
  rw [decrementAll_apply, contents.count_eq]
  have partition := indegree_remove_partition source target edges ready
  omega

/-- Every traversal prefix leaves the residual count plus the unvisited contributions. -/
theorem decrementAll_prefix (source target : α) (edges : List (α × α))
    (visited remaining : List α) (ready : Ready source edges)
    (contents : (visited ++ remaining).Perm (successors source edges)) :
    decrementAll (fun vertex => (indegree vertex edges : Int)) visited target =
      (indegree target (removeNode source edges) : Int) + remaining.count target := by
  rw [decrementAll_apply]
  have partition := indegree_remove_partition source target edges ready
  have counted := contents.count_eq target
  rw [List.count_append] at counted
  omega

theorem decrementAll_prefix_nonneg (source target : α) (edges : List (α × α))
    (visited remaining : List α) (ready : Ready source edges)
    (contents : (visited ++ remaining).Perm (successors source edges)) :
    0 ≤ decrementAll (fun vertex => (indegree vertex edges : Int)) visited target := by
  rw [decrementAll_prefix source target edges visited remaining ready contents]
  omega

/-- Record the vertices whose count becomes zero immediately after their decrement. -/
def discharge (counts : α → Int) : List α → (α → Int) × List α
  | [] => (counts, [])
  | vertex :: rest =>
      let updated := decrement counts vertex
      let result := discharge updated rest
      (result.1, if updated vertex = 0 then vertex :: result.2 else result.2)

theorem discharge_counts (counts : α → Int) (neighbors : List α) :
    (discharge counts neighbors).1 = decrementAll counts neighbors := by
  induction neighbors generalizing counts with
  | nil => rfl
  | cons vertex rest ih => exact ih (decrement counts vertex)

theorem discharge_new (counts : α → Int) (neighbors : List α) (unique : neighbors.Nodup) :
    (discharge counts neighbors).2 =
      neighbors.filter (fun vertex => decide (counts vertex = 1)) := by
  induction neighbors generalizing counts with
  | nil => rfl
  | cons vertex rest ih =>
      have uniqueRest := List.nodup_cons.mp unique
      have unchanged : rest.filter (fun target => decide (decrement counts vertex target = 1)) =
          rest.filter (fun target => decide (counts target = 1)) := by
        apply List.filter_congr
        intro target member
        have different : vertex ≠ target := by
          intro same
          exact uniqueRest.1 (same ▸ member)
        simp [decrement, different]
      simp only [discharge, ih _ uniqueRest.2, unchanged]
      by_cases one : counts vertex = 1
      · simp [decrement, one]
      · have nonzero : counts vertex - 1 ≠ 0 := by omega
        simp [decrement, one, nonzero]

/-- In a deduplicated graph, each successor loses exactly one incoming edge. -/
theorem indegree_remove (source target : α) (edges : List (α × α))
    (ready : Ready source edges) (unique : edges.Nodup) :
    indegree target edges = indegree target (removeNode source edges) +
      if (source, target) ∈ edges then 1 else 0 := by
  rw [indegree_remove_partition source target edges ready]
  have nodup := successors_nodup source edges unique
  by_cases member : target ∈ successors source edges
  · rw [List.count_eq_one_of_mem nodup member]
    simp [(mem_successors source target edges).mp member]
  · simp [List.count_eq_zero.mpr member, ← mem_successors, member]

/-- The zero test after decrement discovers exactly the newly eligible successors. -/
theorem ready_remove_iff (source target : α) (edges : List (α × α))
    (ready : Ready source edges) (unique : edges.Nodup) :
    Ready target (removeNode source edges) ↔
      Ready target edges ∨ ((source, target) ∈ edges ∧ indegree target edges = 1) := by
  have partition := indegree_remove source target edges ready unique
  rw [← indegree_zero_iff, ← indegree_zero_iff]
  by_cases member : (source, target) ∈ edges <;> simp [member] at partition ⊢ <;> omega

def eligible (nodes : List α) (edges : List (α × α)) : List α :=
  nodes.filter (fun vertex => decide (Ready vertex edges))

def newlyReady (source : α) (edges : List (α × α)) : List α :=
  (successors source edges).filter (fun vertex => decide (indegree vertex edges = 1))

theorem mem_eligible (vertex : α) (nodes : List α) (edges : List (α × α)) :
    vertex ∈ eligible nodes edges ↔ vertex ∈ nodes ∧ Ready vertex edges := by
  simp [eligible]

theorem mem_newlyReady (source vertex : α) (edges : List (α × α)) :
    vertex ∈ newlyReady source edges ↔
      (source, vertex) ∈ edges ∧ indegree vertex edges = 1 := by
  simp [newlyReady, mem_successors]

theorem discharge_indegree_new (source : α) (edges : List (α × α)) (neighbors : List α)
    (unique : edges.Nodup) (contents : neighbors.Perm (successors source edges)) :
    ((discharge (fun vertex => (indegree vertex edges : Int)) neighbors).2).Perm
      (newlyReady source edges) := by
  rw [discharge_new _ _ (contents.nodup_iff.mpr (successors_nodup source edges unique))]
  have castOne (n : Nat) : ((n : Int) = 1) ↔ n = 1 := by omega
  simpa only [newlyReady, castOne] using
    contents.filter (fun vertex => decide (indegree vertex edges = 1))

/-- The old queue without its selected vertex and the new arrivals partition the next queue. -/
theorem eligible_remove_perm (source : α) (nodes : List α) (edges : List (α × α))
    (nodesUnique : nodes.Nodup) (edgesUnique : edges.Nodup)
    (endpoints : ∀ edge ∈ edges, edge.1 ∈ nodes ∧ edge.2 ∈ nodes)
    (ready : Ready source edges) :
    (eligible (nodes.erase source) (removeNode source edges)).Perm
      ((eligible nodes edges).erase source ++ newlyReady source edges) := by
  have oldUnique : (eligible nodes edges).Nodup := nodesUnique.filter _
  have newUnique : (newlyReady source edges).Nodup :=
    (successors_nodup source edges edgesUnique).filter _
  have disjoint :
      List.Disjoint ((eligible nodes edges).erase source) (newlyReady source edges) := by
    intro vertex old new
    have oldReady := (mem_eligible vertex nodes edges).mp (List.mem_of_mem_erase old)
    have newCount := (mem_newlyReady source vertex edges).mp new
    have zero := (indegree_zero_iff vertex edges).mpr oldReady.2
    omega
  apply (List.perm_ext_iff_of_nodup ((nodesUnique.erase source).filter _)
    ((oldUnique.erase source).append newUnique disjoint)).mpr
  intro vertex
  change vertex ∈ eligible (nodes.erase source) (removeNode source edges) ↔
    vertex ∈ (eligible nodes edges).erase source ++ newlyReady source edges
  simp only [mem_eligible, nodesUnique.mem_erase_iff, List.mem_append,
    oldUnique.mem_erase_iff, mem_newlyReady, ready_remove_iff source vertex edges ready edgesUnique]
  constructor
  · rintro ⟨⟨different, member⟩, old | new⟩
    · exact Or.inl ⟨different, member, old⟩
    · exact Or.inr new
  · rintro (⟨different, member, old⟩ | new)
    · exact ⟨⟨different, member⟩, Or.inl old⟩
    · exact ⟨⟨ready (source, vertex) new.1, (endpoints (source, vertex) new.1).2⟩, Or.inr new⟩

/-- Pop a ready vertex, visit its adjacency set in any order, and insert the zero crossings.
The resulting queue has exactly the next graph's eligible vertices. -/
theorem discharge_queue (source : α) (nodes : List α) (edges : List (α × α))
    (queued neighbors nextQueue : List α)
    (nodesUnique : nodes.Nodup) (edgesUnique : edges.Nodup)
    (endpoints : ∀ edge ∈ edges, edge.1 ∈ nodes ∧ edge.2 ∈ nodes)
    (queueContents : (source :: queued).Perm (eligible nodes edges))
    (adjacency : neighbors.Perm (successors source edges))
    (insertions : nextQueue.Perm (queued ++
      (discharge (fun vertex => (indegree vertex edges : Int)) neighbors).2)) :
    (discharge (fun vertex => (indegree vertex edges : Int)) neighbors).1 =
        (fun vertex => (indegree vertex (removeNode source edges) : Int)) ∧
      nextQueue.Perm (eligible (nodes.erase source) (removeNode source edges)) := by
  have member : source ∈ eligible nodes edges := queueContents.mem_iff.mp (by simp)
  have ready := ((mem_eligible source nodes edges).mp member).2
  have old : queued.Perm ((eligible nodes edges).erase source) := by
    simpa using queueContents.erase source
  refine ⟨?_, ?_⟩
  · rw [discharge_counts]
    exact decrementAll_indegree source edges neighbors ready adjacency
  · exact (insertions.trans
      (old.append (discharge_indegree_new source edges neighbors edgesUnique adjacency))).trans
        (eligible_remove_perm source nodes edges nodesUnique edgesUnique endpoints ready).symm

end ProjectEulerStatements.TopologicalOrder
