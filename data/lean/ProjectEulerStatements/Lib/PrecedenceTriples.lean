import ProjectEulerStatements.Lib.TopologicalOrder

/-! Expanding a three-position observation with its transitive edge preserves greedy ordering. -/
namespace ProjectEulerStatements.TopologicalOrder
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

theorem respects_edges_congr (left right : List (α × α))
    (same : ∀ edge, edge ∈ left ↔ edge ∈ right) (result : List α) :
    Respects left result ↔ Respects right result := by
  induction result generalizing left right with
  | nil => rfl
  | cons vertex rest ih =>
      have ready : Ready vertex left ↔ Ready vertex right := by
        constructor
        · exact fun valid edge member => valid edge ((same edge).mpr member)
        · exact fun valid edge member => valid edge ((same edge).mp member)
      have removed : ∀ edge, edge ∈ removeNode vertex left ↔ edge ∈ removeNode vertex right := by
        intro edge
        simp only [removeNode, List.mem_filter, same]
      exact and_congr ready (ih _ _ removed)

/-- Duplicate edges and their list order do not affect any constraint or cycle result. -/
theorem order_edges_congr (nodes : List α) (left right : List (α × α))
    (same : ∀ edge, edge ∈ left ↔ edge ∈ right) : order nodes left = order nodes right :=
  order_congr nodes left right (fun result _ => respects_edges_congr left right same result)

/-- Sorting the node enumeration changes neither the least solution nor cycle detection. -/
theorem order_nodes_perm (nodes other : List α) (edges : List (α × α))
    (permutation : nodes.Perm other) : order nodes edges = order other edges := by
  cases first : order nodes edges with
  | none =>
      cases second : order other edges with
      | none => rfl
      | some result =>
          have valid := order_sound other edges result second
          exact False.elim ((order_none_iff nodes edges).mp first
            ⟨result, valid.1.trans permutation.symm, valid.2⟩)
  | some result =>
      have valid := order_sound nodes edges result first
      obtain ⟨output, second⟩ := order_complete other edges result
        ⟨valid.1.trans permutation, valid.2⟩
      have validOther := order_sound other edges output second
      have least := order_minimal nodes edges result output first
        ⟨validOther.1.trans permutation.symm, validOther.2⟩
      have reverse := order_minimal other edges output result second
        ⟨valid.1.trans permutation, valid.2⟩
      rw [second]
      rcases least with same | smaller
      · exact congrArg some same
      · rcases reverse with same | larger
        · exact congrArg some same.symm
        · exact False.elim (asymm smaller larger)

def adjacentEdges (observations : List (α × α × α)) : List (α × α) :=
  observations.flatMap (fun triple => [(triple.1, triple.2.1), (triple.2.1, triple.2.2)])

def expandedEdges (observations : List (α × α × α)) : List (α × α) :=
  observations.flatMap (fun triple =>
    [(triple.1, triple.2.1), (triple.2.1, triple.2.2), (triple.1, triple.2.2)])

omit [LinearOrder α] in
theorem adjacent_subset_expanded (observations : List (α × α × α)) :
    adjacentEdges observations ⊆ expandedEdges observations := by
  intro edge member
  obtain ⟨triple, observed, edgeMember⟩ := List.mem_flatMap.mp member
  exact List.mem_flatMap.mpr ⟨triple, observed, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at edgeMember ⊢
    rcases edgeMember with first | second
    · exact Or.inl first
    · exact Or.inr (Or.inl second)⟩

theorem respects_expansion (observations : List (α × α × α)) (result : List α)
    (vertices : ∀ triple ∈ observations,
      triple.1 ∈ result ∧ triple.2.1 ∈ result ∧ triple.2.2 ∈ result) :
    Respects (expandedEdges observations) result ↔
      Respects (adjacentEdges observations) result := by
  have expandedEndpoints : ∀ edge ∈ expandedEdges observations,
      edge.1 ∈ result ∧ edge.2 ∈ result := by
    intro edge member
    obtain ⟨triple, observed, edgeMember⟩ := List.mem_flatMap.mp member
    have present := vertices triple observed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at edgeMember
    rcases edgeMember with rfl | rfl | rfl
    · exact ⟨present.1, present.2.1⟩
    · exact present.2
    · exact ⟨present.1, present.2.2⟩
  have adjacentEndpoints : ∀ edge ∈ adjacentEdges observations,
      edge.1 ∈ result ∧ edge.2 ∈ result :=
    fun edge member => expandedEndpoints edge (adjacent_subset_expanded observations member)
  rw [respects_iff_indices _ _ expandedEndpoints, respects_iff_indices _ _ adjacentEndpoints]
  constructor
  · exact fun valid edge member => valid edge (adjacent_subset_expanded observations member)
  · intro valid edge member
    obtain ⟨triple, observed, edgeMember⟩ := List.mem_flatMap.mp member
    have first := valid (triple.1, triple.2.1)
      (List.mem_flatMap.mpr ⟨triple, observed, by simp⟩)
    have second := valid (triple.2.1, triple.2.2)
      (List.mem_flatMap.mpr ⟨triple, observed, by simp⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at edgeMember
    rcases edgeMember with rfl | rfl | rfl
    · exact first
    · exact second
    · exact first.trans second

/-- Repeated observations and repeated symbols are allowed, including inconsistent cycles. -/
theorem order_expansion (observations : List (α × α × α)) (nodes : List α)
    (vertices : ∀ triple ∈ observations,
      triple.1 ∈ nodes ∧ triple.2.1 ∈ nodes ∧ triple.2.2 ∈ nodes) :
    order nodes (expandedEdges observations) = order nodes (adjacentEdges observations) := by
  apply order_congr
  intro result permutation
  apply respects_expansion
  intro triple observed
  have present := vertices triple observed
  exact ⟨permutation.mem_iff.mpr present.1,
    permutation.mem_iff.mpr present.2.1, permutation.mem_iff.mpr present.2.2⟩

end ProjectEulerStatements.TopologicalOrder
