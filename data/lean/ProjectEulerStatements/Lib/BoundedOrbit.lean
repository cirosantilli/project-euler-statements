import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Function.Iterate
import Lean.Elab.Tactic.Omega

/-! First-repeat walks terminate in every proved finite invariant interval. -/
namespace ProjectEulerStatements.BoundedOrbit
set_option Elab.async false

def Within (bound : Nat) (seen : List Nat) : Prop := ∀ n ∈ seen, n ≤ bound

theorem length_le (bound : Nat) (seen : List Nat) (distinct : seen.Nodup)
    (inside : Within bound seen) : seen.length ≤ bound + 1 := by
  have subset : seen.toFinset ⊆ Finset.range (bound + 1) := by
    intro n member
    exact Finset.mem_range.mpr (by have := inside n (List.mem_toFinset.mp member); omega)
  simpa only [List.toFinset_card_of_nodup distinct, Finset.card_range] using
    Finset.card_le_card subset

theorem append_distinct (seen : List Nat) (current : Nat)
    (distinct : seen.Nodup) (fresh : current ∉ seen) : (seen ++ [current]).Nodup := by
  rw [List.nodup_append]
  refine ⟨distinct, by simp, ?_⟩
  intro n member m only same
  have equal : m = current := List.mem_singleton.mp only
  exact fresh ((same.trans equal) ▸ member)

theorem append_within (bound : Nat) (seen : List Nat) (current : Nat)
    (inside : Within bound seen) (bounded : current ≤ bound) :
    Within bound (seen ++ [current]) := by
  intro n member
  rcases List.mem_append.mp member with before | here
  · exact inside n before
  · simpa only [List.mem_singleton.mp here] using bounded

theorem room (bound current : Nat) (seen : List Nat)
    (distinct : seen.Nodup) (inside : Within bound seen)
    (bounded : current ≤ bound) (fresh : current ∉ seen) : seen.length < bound + 1 := by
  have enough := length_le bound (seen ++ [current]) (append_distinct seen current distinct fresh)
    (append_within bound seen current inside bounded)
  simp only [List.length_append, List.length_singleton] at enough
  omega

/-- The only stop condition is repetition; the interval is used to prove termination. -/
def walk (f : Nat → Nat) (bound : Nat) (closed : ∀ n ≤ bound, f n ≤ bound)
    (current : Nat) (seen : List Nat) (bounded : current ≤ bound)
    (distinct : seen.Nodup) (inside : Within bound seen) : List Nat :=
  if fresh : current ∈ seen then seen
  else walk f bound closed (f current) (seen ++ [current]) (closed current bounded)
    (append_distinct seen current distinct fresh) (append_within bound seen current inside bounded)
termination_by bound + 1 - seen.length
decreasing_by
  have enough := room bound current seen distinct inside bounded fresh
  simp only [List.length_append, List.length_singleton]
  omega

/-- A finite trace records the actual first-repeat control flow, with no step count. -/
inductive Trace (f : Nat → Nat) : Nat → List Nat → List Nat → Prop
  | done {current seen} : current ∈ seen → Trace f current seen seen
  | step {current seen result} : current ∉ seen →
      Trace f (f current) (seen ++ [current]) result → Trace f current seen result

theorem walk_trace (f : Nat → Nat) (bound : Nat) (closed : ∀ n ≤ bound, f n ≤ bound)
    (current : Nat) (seen : List Nat) (bounded : current ≤ bound)
    (distinct : seen.Nodup) (inside : Within bound seen) :
    Trace f current seen (walk f bound closed current seen bounded distinct inside) := by
  rw [walk]
  split
  · exact .done ‹_›
  · exact .step ‹_› (walk_trace f bound closed (f current) (seen ++ [current])
      (closed current bounded) (append_distinct seen current distinct ‹_›)
      (append_within bound seen current inside bounded))
termination_by bound + 1 - seen.length
decreasing_by
  have enough := room bound current seen distinct inside bounded ‹_›
  simp only [List.length_append, List.length_singleton]
  omega

theorem Trace.unique {f : Nat → Nat} {current : Nat} {seen left right : List Nat}
    (first : Trace f current seen left) (second : Trace f current seen right) : left = right := by
  induction first with
  | done present =>
      cases second with
      | done => rfl
      | step fresh => exact False.elim (fresh present)
  | step fresh rest ih =>
      cases second with
      | done present => exact False.elim (fresh present)
      | step _ next => exact ih next

theorem Trace.prefix {f : Nat → Nat} {current : Nat} {seen result : List Nat}
    (trace : Trace f current seen result) : seen <+: result := by
  induction trace with
  | done => exact List.prefix_refl _
  | @step current seen result _ _ ih =>
      exact (List.prefix_append seen [current]).trans ih

theorem Trace.distinct {f : Nat → Nat} {current : Nat} {seen result : List Nat}
    (trace : Trace f current seen result) (distinct : seen.Nodup) : result.Nodup := by
  induction trace with
  | done => exact distinct
  | step fresh _ ih => exact ih (append_distinct _ _ distinct fresh)

theorem Trace.current_mem {f : Nat → Nat} {current : Nat} {seen result : List Nat}
    (trace : Trace f current seen result) : current ∈ result := by
  cases trace with
  | done present => exact present
  | step _ rest => exact rest.prefix.subset (by simp)

theorem Trace.successor_mem {f : Nat → Nat} {current : Nat} {seen result : List Nat}
    (trace : Trace f current seen result) (n : Nat) (member : n ∈ result) (new : n ∉ seen) :
    f n ∈ result := by
  induction trace with
  | done => exact False.elim (new member)
  | @step current seen result fresh rest ih =>
      by_cases same : n = current
      · subst n
        exact rest.current_mem
      · apply ih member
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨new, same⟩

theorem Trace.reachable {f : Nat → Nat} {current : Nat} {seen result : List Nat}
    (trace : Trace f current seen result) (n : Nat) (member : n ∈ result) (new : n ∉ seen) :
    ∃ steps : Nat, f^[steps] current = n := by
  induction trace with
  | done => exact False.elim (new member)
  | @step current seen result fresh rest ih =>
      by_cases same : n = current
      · exact ⟨0, same.symm⟩
      · obtain ⟨steps, reached⟩ := ih member
          (by simpa only [List.mem_append, List.mem_singleton, not_or] using And.intro new same)
        exact ⟨steps + 1, by simpa only [Function.iterate_succ_apply] using reached⟩

/-- A complete first-repeat path contains precisely the full forward orbit. -/
theorem Trace.mem_iff {f : Nat → Nat} {start n : Nat} {result : List Nat}
    (trace : Trace f start [] result) : n ∈ result ↔ ∃ steps : Nat, f^[steps] start = n := by
  constructor
  · intro member
    exact trace.reachable n member (by simp)
  · rintro ⟨steps, rfl⟩
    induction steps with
    | zero => exact trace.current_mem
    | succ steps ih =>
        simpa only [Function.iterate_succ_apply'] using
          trace.successor_mem _ ih (by simp)

def segment (f : Nat → Nat) (start count : Nat) : List Nat :=
  (List.range count).map (fun steps => f^[steps] start)

@[simp] theorem segment_length (f : Nat → Nat) (start count : Nat) :
    (segment f start count).length = count := by simp [segment]

theorem segment_succ (f : Nat → Nat) (start count : Nat) :
    segment f start (count + 1) = [start] ++ segment f (f start) count := by
  simp only [segment, List.range_succ_eq_map, List.map_cons, List.map_map,
    Function.comp_def, Function.iterate_zero_apply, Function.iterate_succ_apply]
  rfl

theorem segment_append (f : Nat → Nat) (start left right : Nat) :
    segment f start (left + right) =
      segment f start left ++ segment f (f^[left] start) right := by
  induction left generalizing start with
  | zero => simp [segment]
  | succ left ih =>
      simp only [Nat.succ_add, segment_succ, ih, List.append_assoc,
        Function.iterate_succ_apply]

theorem segment_drop (f : Nat → Nat) (start count first : Nat) (before : first ≤ count) :
    (segment f start count).drop first = segment f (f^[first] start) (count - first) := by
  have split : count = first + (count - first) := by omega
  have empty : (segment f start first).drop first = [] :=
    List.drop_eq_nil_of_le (by rw [segment_length])
  conv_lhs => rw [split, segment_append]
  simp only [List.drop_append, segment_length, Nat.sub_self, List.drop_zero, empty,
    List.nil_append]

theorem mem_segment (f : Nat → Nat) (start count n : Nat) :
    n ∈ segment f start count ↔ ∃ steps < count, f^[steps] start = n := by
  simp only [segment, List.mem_map, List.mem_range]

/-- A trace extends its visited prefix by consecutive function iterates. -/
theorem Trace.remaining {f : Nat → Nat} {current : Nat} {seen result : List Nat}
    (trace : Trace f current seen result) :
    ∃ count, result = seen ++ segment f current count ∧ f^[count] current ∈ result := by
  induction trace with
  | done present => exact ⟨0, by simp [segment], present⟩
  | @step current seen result fresh rest ih =>
      obtain ⟨count, expanded, repeated⟩ := ih
      refine ⟨count + 1, ?_, ?_⟩
      · simpa only [segment_succ, List.append_assoc] using expanded
      · simpa only [Function.iterate_succ_apply] using repeated

theorem Trace.complete_segment {f : Nat → Nat} {start : Nat} {result : List Nat}
    (trace : Trace f start [] result) :
    result = segment f start result.length ∧ f^[result.length] start ∈ result := by
  obtain ⟨count, expanded, repeated⟩ := trace.remaining
  simp only [List.nil_append] at expanded
  have sized : result.length = count := by rw [expanded, segment_length]
  simpa only [sized] using And.intro expanded repeated

end ProjectEulerStatements.BoundedOrbit
