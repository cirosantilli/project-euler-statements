import ProjectEulerStatements.Lib.HeapqSchedule

/-! A left-child ancestor path reaches the leftmost descendant at each level.
This characterizes which parent paths can precede one another in cache traversal. -/
namespace ProjectEulerStatements.MinHeap
open FormalSW.PyAst
set_option Elab.async false

def depth (node : Nat) : Nat := (node + 1).log2

theorem Child.depth_step {parent child : Nat} (edge : Child parent child) :
    depth child = depth parent + 1 := by
  unfold depth
  apply (Nat.log2_eq_iff (by omega)).mpr
  have lower : 2 ^ (parent + 1).log2 ≤ parent + 1 := Nat.log2_self_le (by omega)
  have upper : parent + 1 < 2 ^ ((parent + 1).log2 + 1) := Nat.lt_log2_self
  simp only [Nat.pow_succ] at upper ⊢
  unfold Child at edge
  constructor <;> omega

theorem Descendant.scaled {root node : Nat} (below : Descendant root node) :
    ∃ distance, depth node = depth root + distance ∧ (root + 1) * 2 ^ distance ≤ node + 1 := by
  induction below with
  | refl => exact ⟨0, by simp, by simp⟩
  | @child parent node earlier edge ih =>
      obtain ⟨distance, level, lower⟩ := ih
      refine ⟨distance + 1, by rw [edge.depth_step, level]; omega, ?_⟩
      have bound : 2 * (parent + 1) ≤ node + 1 := by unfold Child at edge; omega
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      omega

theorem parentPath_geometry (leaf ancestor : Nat) (member : ancestor ∈ Heapq.parentPath leaf) :
    Descendant ancestor leaf ∧ ∃ distance,
      depth leaf = depth ancestor + distance ∧ leaf + 1 = (ancestor + 1) * 2 ^ distance := by
  rw [Heapq.parentPath] at member
  rcases List.mem_cons.mp member with same | tail
  · subst ancestor
    exact ⟨.refl, 0, by simp, by simp⟩
  · by_cases odd : leaf % 2 = 1
    · rw [if_pos odd] at tail
      obtain ⟨below, distance, level, equation⟩ := parentPath_geometry (leaf / 2) ancestor tail
      have edge : Child (leaf / 2) leaf := Or.inl (by omega)
      refine ⟨below.child edge, distance + 1, ?_, ?_⟩
      · rw [edge.depth_step, level]
        omega
      · have doubled : leaf + 1 = 2 * (leaf / 2 + 1) := by omega
        rw [Nat.pow_succ, ← Nat.mul_assoc, ← equation]
        omega
    · simp [odd] at tail
termination_by leaf
decreasing_by apply Nat.div_lt_self <;> omega

theorem parentPath_same_level_le (leaf ancestor node : Nat)
    (member : ancestor ∈ Heapq.parentPath leaf) (below : Descendant ancestor node)
    (sameLevel : depth node = depth leaf) : leaf ≤ node := by
  obtain ⟨_, distance, level, equation⟩ := parentPath_geometry leaf ancestor member
  obtain ⟨otherDistance, otherLevel, lower⟩ := below.scaled
  have same : otherDistance = distance := by omega
  subst otherDistance
  omega

theorem parentPath_next_level_le (leaf ancestor node : Nat)
    (member : ancestor ∈ Heapq.parentPath leaf) (below : Descendant ancestor node)
    (nextLevel : depth node = depth leaf + 1) : 2 * leaf + 1 ≤ node := by
  obtain ⟨_, distance, level, equation⟩ := parentPath_geometry leaf ancestor member
  obtain ⟨otherDistance, otherLevel, lower⟩ := below.scaled
  have next : otherDistance = distance + 1 := by omega
  rw [next, Nat.pow_succ, ← Nat.mul_assoc, ← equation] at lower
  omega

theorem parentPaths_same_level (first second : Nat) (sameLevel : depth second = depth first)
    (earlier : second < first) :
    ∀ ancestor ∈ Heapq.parentPath first, ∀ node ∈ Heapq.parentPath second,
      ¬Descendant ancestor node := by
  intro ancestor firstMember node secondMember below
  have reaches := below.trans (parentPath_geometry second node secondMember).1
  have lower := parentPath_same_level_le first ancestor second firstMember reaches sameLevel
  omega

theorem parentPaths_next_level (first second : Nat) (nextLevel : depth second = depth first + 1)
    (earlier : second < 2 * first + 1) :
    ∀ ancestor ∈ Heapq.parentPath first, ∀ node ∈ Heapq.parentPath second,
      ¬Descendant ancestor node := by
  intro ancestor firstMember node secondMember below
  have reaches := below.trans (parentPath_geometry second node secondMember).1
  have lower := parentPath_next_level_le first ancestor second firstMember reaches nextLevel
  omega

end ProjectEulerStatements.MinHeap
