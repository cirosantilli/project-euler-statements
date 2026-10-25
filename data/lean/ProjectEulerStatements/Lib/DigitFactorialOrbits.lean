import ProjectEulerStatements.Lib.DigitFactorialChains
import Mathlib.Dynamics.PeriodicPts.Defs

/-! Orbit cardinalities justify memoizing tails and assigning a common length to cycles. -/
namespace ProjectEulerStatements.DigitFactorialChains
open BoundedOrbit
set_option Elab.async false

def orbit (start : Nat) : Finset Nat := (path start).toFinset

theorem mem_orbit (start n : Nat) :
    n ∈ orbit start ↔ ∃ steps : Nat, nextTerm^[steps] start = n := by
  simpa only [orbit, List.mem_toFinset] using path_mem_iff start n

@[simp] theorem orbit_card (start : Nat) : (orbit start).card = chainLen start :=
  List.toFinset_card_of_nodup (path_distinct start)

theorem start_mem_orbit (start : Nat) : start ∈ orbit start :=
  (mem_orbit start start).mpr ⟨0, rfl⟩

theorem orbit_subset {start n : Nat} (reached : n ∈ orbit start) : orbit n ⊆ orbit start := by
  obtain ⟨before, rfl⟩ := (mem_orbit start n).mp reached
  intro m member
  obtain ⟨after, rfl⟩ := (mem_orbit _ m).mp member
  exact (mem_orbit _ _).mpr ⟨after + before, Function.iterate_add_apply ..⟩

theorem orbit_eq_of_mutual {start n : Nat}
    (forward : n ∈ orbit start) (backward : start ∈ orbit n) : orbit start = orbit n :=
  Finset.Subset.antisymm (orbit_subset backward) (orbit_subset forward)

theorem orbit_step (start : Nat) : orbit start = insert start (orbit (nextTerm start)) := by
  ext n
  rw [mem_orbit, Finset.mem_insert, mem_orbit]
  constructor
  · rintro ⟨steps, reached⟩
    cases steps with
    | zero => exact Or.inl reached.symm
    | succ steps => exact Or.inr ⟨steps, reached⟩
  · rintro (rfl | ⟨steps, reached⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨steps + 1, reached⟩

theorem orbit_within (start : Nat) (known : Nat → Prop) (initial : known start)
    (closed : ∀ n, known n → known (nextTerm n)) : ∀ n ∈ orbit start, known n := by
  intro n member
  obtain ⟨steps, rfl⟩ := (mem_orbit start n).mp member
  clear member
  induction steps with
  | zero => exact initial
  | succ steps ih => simpa only [Function.iterate_succ_apply'] using closed _ ih

/-- A new tail node adds exactly one distinct term before an already known orbit. -/
theorem chainLen_of_fresh (start : Nat) (known : Nat → Prop)
    (fresh : ¬ known start) (following : known (nextTerm start))
    (closed : ∀ n, known n → known (nextTerm n)) :
    chainLen start = chainLen (nextTerm start) + 1 := by
  have outside : start ∉ orbit (nextTerm start) := by
    intro member
    exact fresh (orbit_within _ known following closed _ member)
  rw [← orbit_card, orbit_step, Finset.card_insert_of_notMem outside, orbit_card]

theorem orbit_periodic (start count : Nat) (positive : 0 < count)
    (periodic : nextTerm^[count] start = start) :
    orbit start = (segment nextTerm start count).toFinset := by
  have period : Function.IsPeriodicPt nextTerm count start := periodic
  ext n
  rw [mem_orbit, List.mem_toFinset, mem_segment]
  constructor
  · rintro ⟨steps, reached⟩
    exact ⟨steps % count, Nat.mod_lt _ positive, (period.iterate_mod_apply steps).trans reached⟩
  · rintro ⟨steps, _, reached⟩
    exact ⟨steps, reached⟩

/-- Every member of a duplicate-free closed cycle has the complete cycle's length. -/
theorem chainLen_of_cycle (start count n : Nat) (positive : 0 < count)
    (periodic : nextTerm^[count] start = start)
    (distinct : (segment nextTerm start count).Nodup)
    (member : n ∈ segment nextTerm start count) : chainLen n = count := by
  obtain ⟨steps, before, rfl⟩ := (mem_segment _ _ _ _).mp member
  have forward : nextTerm^[steps] start ∈ orbit start := (mem_orbit _ _).mpr ⟨steps, rfl⟩
  have backward : start ∈ orbit (nextTerm^[steps] start) := by
    apply (mem_orbit _ _).mpr
    refine ⟨count - steps, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel before.le]
    exact periodic
  rw [← orbit_card, ← orbit_eq_of_mutual forward backward,
    orbit_periodic start count positive periodic, List.toFinset_card_of_nodup distinct,
    segment_length]

theorem cycle_closed (start count : Nat) (positive : 0 < count)
    (periodic : nextTerm^[count] start = start) (n : Nat)
    (member : n ∈ segment nextTerm start count) :
    nextTerm n ∈ segment nextTerm start count := by
  have reached : n ∈ orbit start := by
    rw [orbit_periodic start count positive periodic]
    exact List.mem_toFinset.mpr member
  have following : nextTerm n ∈ orbit start :=
    orbit_subset reached ((mem_orbit _ _).mpr ⟨1, rfl⟩)
  simpa only [orbit_periodic start count positive periodic, List.mem_toFinset] using following

/-- The repeated position separates a first-repeat path into its tail and complete cycle. -/
theorem chainLen_on_cycle (start first n : Nat) (before : first < chainLen start)
    (repeated : nextTerm^[chainLen start] start = nextTerm^[first] start)
    (member : n ∈ (path start).drop first) : chainLen n = chainLen start - first := by
  let count := chainLen start - first
  let cycleStart := nextTerm^[first] start
  have sized : first + count = chainLen start := by dsimp [count]; omega
  have expanded : path start = segment nextTerm start first ++
      segment nextTerm cycleStart count := by
    calc
      path start = segment nextTerm start (chainLen start) :=
        (path_trace start).complete_segment.1
      _ = _ := by rw [← sized, segment_append]
  have distinct : (segment nextTerm cycleStart count).Nodup := by
    have allDistinct := path_distinct start
    rw [expanded, List.nodup_append] at allDistinct
    exact allDistinct.2.1
  have periodic : nextTerm^[count] cycleStart = cycleStart := by
    dsimp only [cycleStart]
    rw [← Function.iterate_add_apply, Nat.add_comm count first, sized]
    exact repeated
  have suffix : (path start).drop first = segment nextTerm cycleStart count := by
    rw [(path_trace start).complete_segment.1]
    exact segment_drop nextTerm start (chainLen start) first before.le
  apply chainLen_of_cycle cycleStart count n (by dsimp [count]; omega) periodic distinct
  simpa only [suffix] using member

end ProjectEulerStatements.DigitFactorialChains
