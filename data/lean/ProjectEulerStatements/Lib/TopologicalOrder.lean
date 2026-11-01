import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Lex

/-! Greedy ordering of finite precedence constraints, with no fixed alphabet or iteration budget. -/
namespace ProjectEulerStatements.TopologicalOrder
variable {α : Type*} [LinearOrder α]
set_option Elab.async false

def removeNode (v : α) (edges : List (α × α)) : List (α × α) :=
  edges.filter (fun edge => decide (edge.1 ≠ v ∧ edge.2 ≠ v))

def Ready (v : α) (edges : List (α × α)) : Prop := ∀ edge ∈ edges, edge.2 ≠ v

instance (v : α) (edges : List (α × α)) : Decidable (Ready v edges) := by
  unfold Ready
  infer_instance

def Respects (edges : List (α × α)) : List α → Prop
  | [] => True
  | v :: rest => Ready v edges ∧ Respects (removeNode v edges) rest

def Valid (nodes : List α) (edges : List (α × α)) (result : List α) : Prop :=
  result.Perm nodes ∧ Respects edges result

theorem remove_comm (a b : α) (edges : List (α × α)) :
    removeNode a (removeNode b edges) = removeNode b (removeNode a edges) :=
  List.filter_comm _ _ _

theorem ready_remove (v x : α) (edges : List (α × α)) (ready : Ready v edges) :
    Ready v (removeNode x edges) := by
  intro edge member
  exact ready edge (List.mem_filter.mp member).1

/-- Deleting a vertex and its incident constraints preserves a valid relative ordering. -/
theorem respects_erase (edges : List (α × α)) (result : List α) (x : α)
    (valid : Respects edges result) : Respects (removeNode x edges) (result.erase x) := by
  induction result generalizing edges with
  | nil => trivial
  | cons v rest ih =>
      by_cases same : x = v
      · subst x
        simpa only [List.erase_cons_head] using valid.2
      · rw [List.erase_cons_tail (by simpa using Ne.symm same)]
        exact ⟨ready_remove v x edges valid.1,
          by rw [remove_comm]; exact ih (removeNode v edges) valid.2⟩

/-- Removing incoming-free vertices is equivalent to every edge pointing forward in the result. -/
theorem respects_iff_indices (edges : List (α × α)) (result : List α)
    (endpoints : ∀ edge ∈ edges, edge.1 ∈ result ∧ edge.2 ∈ result) :
    Respects edges result ↔ ∀ edge ∈ edges, result.idxOf edge.1 < result.idxOf edge.2 := by
  induction result generalizing edges with
  | nil =>
      constructor
      · intro _ edge member
        have impossible := (endpoints edge member).1
        simp at impossible
      · intro _
        trivial
  | cons v rest ih =>
      have retained : ∀ edge ∈ removeNode v edges, edge.1 ∈ rest ∧ edge.2 ∈ rest := by
        intro edge member
        simp only [removeNode, List.mem_filter, decide_eq_true_eq] at member
        have old := endpoints edge member.1
        exact ⟨(List.mem_cons.mp old.1).resolve_left member.2.1,
          (List.mem_cons.mp old.2).resolve_left member.2.2⟩
      constructor
      · intro valid edge member
        have rightNe := valid.1 edge member
        by_cases leftEq : edge.1 = v
        · simp [leftEq, Ne.symm rightNe]
        · have remaining := (ih (removeNode v edges) retained).mp valid.2 edge
            (List.mem_filter.mpr ⟨member, by simpa using And.intro leftEq rightNe⟩)
          simpa [List.idxOf_cons, Ne.symm leftEq, Ne.symm rightNe] using Nat.succ_lt_succ remaining
      · intro forward
        refine ⟨?_, (ih (removeNode v edges) retained).mpr ?_⟩
        · intro edge member same
          have impossible := forward edge member
          simp [same] at impossible
        · intro edge member
          simp only [removeNode, List.mem_filter, decide_eq_true_eq] at member
          have old := forward edge member.1
          simpa [List.idxOf_cons, Ne.symm member.2.1, Ne.symm member.2.2] using old

def choose (nodes : List α) (edges : List (α × α)) : Option α :=
  (nodes.filter (fun v => decide (Ready v edges))).min?

theorem choose_spec (nodes : List α) (edges : List (α × α)) (v : α)
    (chosen : choose nodes edges = some v) :
    v ∈ nodes ∧ Ready v edges ∧ ∀ w ∈ nodes, Ready w edges → v ≤ w := by
  have minimum := List.min?_eq_some_iff.mp chosen
  have member := List.mem_filter.mp minimum.1
  refine ⟨member.1, of_decide_eq_true member.2, ?_⟩
  intro w inside ready
  exact minimum.2 w (List.mem_filter.mpr ⟨inside, by simpa⟩)

def order (nodes : List α) (edges : List (α × α)) : Option (List α) :=
  if nodes = [] then some []
  else match _chosen : choose nodes edges with
    | none => none
    | some v => (v :: ·) <$> order (nodes.erase v) (removeNode v edges)
termination_by nodes.length
decreasing_by
  have member := (choose_spec nodes edges v _chosen).1
  rw [List.length_erase_of_mem member]
  have := List.length_pos_of_mem member
  omega

theorem order_sound (nodes : List α) (edges : List (α × α)) (result : List α)
    (returned : order nodes edges = some result) : Valid nodes edges result := by
  rw [order] at returned
  split at returned
  · rename_i empty
    simp only [Option.some.injEq] at returned
    subst result
    subst nodes
    exact ⟨List.Perm.refl _, trivial⟩
  · cases chosen : choose nodes edges with
    | none => rw [chosen] at returned; contradiction
    | some v =>
        rw [chosen] at returned
        obtain ⟨rest, recursive, rfl⟩ := Option.map_eq_some_iff.mp returned
        have spec := choose_spec nodes edges v chosen
        have sound := order_sound (nodes.erase v) (removeNode v edges) rest recursive
        exact ⟨(sound.1.cons v).trans (List.perm_cons_erase spec.1).symm, spec.2.1, sound.2⟩
termination_by nodes.length
decreasing_by
  rw [List.length_erase_of_mem (choose_spec nodes edges v chosen).1]
  have := List.length_pos_of_mem (choose_spec nodes edges v chosen).1
  omega

theorem order_complete (nodes : List α) (edges : List (α × α)) (witness : List α)
    (valid : Valid nodes edges witness) : ∃ result, order nodes edges = some result := by
  by_cases empty : nodes = []
  · exact ⟨[], by rw [order, if_pos empty]⟩
  · cases witness with
    | nil =>
        have impossible := valid.1.length_eq
        exact False.elim (empty (List.length_eq_zero_iff.mp impossible.symm))
    | cons v rest =>
        have member : v ∈ nodes := valid.1.subset (by simp)
        have ready := valid.2.1
        cases chosen : choose nodes edges with
        | none =>
            have noReady : nodes.filter (fun w => decide (Ready w edges)) = [] :=
              List.min?_eq_none_iff.mp chosen
            have present : v ∈ nodes.filter (fun w => decide (Ready w edges)) :=
              List.mem_filter.mpr ⟨member, by simpa⟩
            simp [noReady] at present
        | some x =>
            have retained : Valid (nodes.erase x) (removeNode x edges) ((v :: rest).erase x) :=
              ⟨valid.1.erase x, respects_erase edges (v :: rest) x valid.2⟩
            obtain ⟨result, returned⟩ :=
              order_complete (nodes.erase x) (removeNode x edges) _ retained
            exact ⟨x :: result, by rw [order, if_neg empty, chosen]; simp [returned]⟩
termination_by nodes.length
decreasing_by
  rw [List.length_erase_of_mem (choose_spec nodes edges x chosen).1]
  have := List.length_pos_of_mem (choose_spec nodes edges x chosen).1
  omega

theorem order_none_iff (nodes : List α) (edges : List (α × α)) :
    order nodes edges = none ↔ ¬ ∃ result, Valid nodes edges result := by
  constructor
  · intro missing ⟨witness, valid⟩
    obtain ⟨result, returned⟩ := order_complete nodes edges witness valid
    rw [missing] at returned
    contradiction
  · intro absent
    cases returned : order nodes edges with
    | none => rfl
    | some result => exact False.elim (absent ⟨result, order_sound nodes edges result returned⟩)

/-- At every position the greedy result is least among all valid permutations. -/
theorem order_minimal (nodes : List α) (edges : List (α × α)) (result other : List α)
    (returned : order nodes edges = some result) (valid : Valid nodes edges other) :
    result = other ∨ List.Lex (· < ·) result other := by
  rw [order] at returned
  split at returned
  · rename_i empty
    simp only [Option.some.injEq] at returned
    subst result
    have length := valid.1.length_eq
    rw [empty] at length
    left
    exact (List.length_eq_zero_iff.mp length).symm
  · rename_i nonempty
    cases chosen : choose nodes edges with
    | none => rw [chosen] at returned; contradiction
    | some v =>
        rw [chosen] at returned
        obtain ⟨rest, recursive, rfl⟩ := Option.map_eq_some_iff.mp returned
        cases other with
        | nil => exact False.elim (nonempty (List.length_eq_zero_iff.mp valid.1.length_eq.symm))
        | cons w remaining =>
            have member : w ∈ nodes := valid.1.subset (by simp)
            have lower := (choose_spec nodes edges v chosen).2.2 w member valid.2.1
            by_cases same : v = w
            · subst w
              have retained : Valid (nodes.erase v) (removeNode v edges) remaining :=
                ⟨by simpa only [List.erase_cons_head] using valid.1.erase v, valid.2.2⟩
              rcases order_minimal (nodes.erase v) (removeNode v edges)
                  rest remaining recursive retained
                  with equal | smaller
              · exact Or.inl (by rw [equal])
              · exact Or.inr (List.Lex.cons smaller)
            · right
              apply List.Lex.rel
              rcases lt_or_eq_of_le lower with smaller | equal
              · exact smaller
              · contradiction
termination_by nodes.length
decreasing_by
  rw [List.length_erase_of_mem (choose_spec nodes edges v chosen).1]
  have := List.length_pos_of_mem (choose_spec nodes edges v chosen).1
  omega

/-- Redundant constraints do not change either the least result or detection of impossibility. -/
theorem order_congr (nodes : List α) (left right : List (α × α))
    (same : ∀ result, result.Perm nodes → (Respects left result ↔ Respects right result)) :
    order nodes left = order nodes right := by
  cases first : order nodes left with
  | none =>
      cases second : order nodes right with
      | none => rfl
      | some result =>
          have valid := order_sound nodes right result second
          have impossible := (order_none_iff nodes left).mp first
          exact False.elim (impossible ⟨result, valid.1, (same result valid.1).mpr valid.2⟩)
  | some x =>
      have validX := order_sound nodes left x first
      cases second : order nodes right with
      | none =>
          have impossible := (order_none_iff nodes right).mp second
          exact False.elim (impossible ⟨x, validX.1, (same x validX.1).mp validX.2⟩)
      | some y =>
          have validY := order_sound nodes right y second
          have leastX := order_minimal nodes left x y first
            ⟨validY.1, (same y validY.1).mpr validY.2⟩
          have leastY := order_minimal nodes right y x second
            ⟨validX.1, (same x validX.1).mp validX.2⟩
          rcases leastX with equal | smaller
          · exact congrArg some equal
          · rcases leastY with equal | larger
            · exact congrArg some equal.symm
            · exact False.elim (asymm smaller larger)

/-- An edge implied by two existing edges does not add an ordering restriction. -/
theorem respects_transitive_edge (edges : List (α × α)) (result : List α) (a b c : α)
    (first : (a, b) ∈ edges) (second : (b, c) ∈ edges)
    (endpoints : ∀ edge ∈ edges, edge.1 ∈ result ∧ edge.2 ∈ result) :
    Respects ((a, c) :: edges) result ↔ Respects edges result := by
  have larger : ∀ edge ∈ (a, c) :: edges, edge.1 ∈ result ∧ edge.2 ∈ result := by
    intro edge member
    rcases List.mem_cons.mp member with same | old
    · subst edge
      exact ⟨(endpoints (a, b) first).1, (endpoints (b, c) second).2⟩
    · exact endpoints edge old
  rw [respects_iff_indices _ _ larger, respects_iff_indices _ _ endpoints]
  constructor
  · intro valid edge member
    exact valid edge (List.mem_cons_of_mem _ member)
  · intro valid edge member
    rcases List.mem_cons.mp member with same | old
    · subst edge
      exact lt_trans (valid (a, b) first) (valid (b, c) second)
    · exact valid edge old

end ProjectEulerStatements.TopologicalOrder
