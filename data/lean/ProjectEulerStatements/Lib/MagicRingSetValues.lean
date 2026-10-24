import ProjectEulerStatements.Lib.MagicRingOuterValues
import ProjectEulerStatements.Lib.MagicRingSearch
import lang.py.FormalSW.SetDifferenceCalls

/-! Set equality and cardinality certify exactly the complete forced outer assignments. -/
namespace ProjectEulerStatements.MagicRing
open FormalSW.PyAst
set_option Elab.async false

def ints (values : List Nat) : List Int := values.map (fun value : Nat => (value : Int))

theorem ring_complement_ints {n : Nat} (ring : Ring n) (value : Int) :
    value ∈ ints ring.outer ↔ value ∈ ints (labels n) ∧ value ∉ ints ring.inner := by
  constructor
  · intro present
    obtain ⟨natural, belongs, equal⟩ := List.mem_map.mp present
    subst value
    simpa only [ints, List.mem_map, Int.natCast_inj, exists_eq_right] using
      (outer_complement ring natural).mp belongs
  · rintro ⟨present, absent⟩
    obtain ⟨natural, belongs, equal⟩ := List.mem_map.mp present
    subst value
    have absentNatural : natural ∉ ring.inner := by
      intro inside
      exact absent (List.mem_map.mpr ⟨natural, inside, rfl⟩)
    exact List.mem_map.mpr
      ⟨natural, (outer_complement ring natural).mpr ⟨belongs, absentNatural⟩, rfl⟩

theorem complement_members (n : Nat) (inner : List Nat) (value : Nat) :
    ScalarSet.contains
      (ScalarSet.difference (IntegerSets.entries (ints (labels n)))
        (IntegerSets.entries (ints inner))) (.int value) =
      decide (value ∈ labels n ∧ value ∉ inner) := by
  simp only [IntegerSets.contains_difference, ints, List.mem_map, Int.natCast_inj, exists_eq_right]

theorem validation_members (n : Nat) (inner : List Nat) (outer : List Int) :
    ScalarSet.compare .eq (IntegerSets.entries outer)
      (ScalarSet.difference (IntegerSets.entries (ints (labels n)))
        (IntegerSets.entries (ints inner))) = true ↔
      ∀ value, value ∈ outer ↔ value ∈ ints (labels n) ∧ value ∉ ints inner := by
  rw [IntegerSets.difference_entries]
  simpa only [IntegerSets.entries, List.mem_filter, List.mem_eraseDups, decide_eq_true_eq] using
    IntegerSets.compare_ints_eq outer.eraseDups
      ((ints (labels n)).eraseDups.filter (fun value => decide (value ∉ ints inner)))

theorem validated_ring (n : Nat) (inner : List Nat) (size : inner.length = n)
    (innerDistinct : inner.Nodup) (innerSubset : ∀ value ∈ inner, value ∈ labels n)
    (full : (builtOuter n inner).length = n)
    (cardinality : (IntegerSets.entries (builtOuter n inner)).length = n)
    (same : ScalarSet.compare .eq (IntegerSets.entries (builtOuter n inner))
      (ScalarSet.difference (IntegerSets.entries (ints (labels n)))
        (IntegerSets.entries (ints inner))) = true) :
    ∃ ring : Ring n, ring.inner = inner ∧ builtOuter n inner = ints ring.outer ∧
      ring ∈ optimizedRings n := by
  have distinct : (builtOuter n inner).Nodup :=
    (IntegerSets.entries_length_eq _).mp (cardinality.trans full.symm)
  obtain ⟨ring, innerEq, outerEq, forced⟩ := builtOuter_pack n inner size innerDistinct innerSubset
    full distinct ((validation_members n inner _).mp same)
  exact ⟨ring, innerEq, outerEq, (mem_optimizedRings ring).mpr forced⟩

theorem magic_validation {n : Nat} (ring : Ring n) (positive : 0 < n)
    (sum : Nat) (magic : Magic ring sum) :
    (builtOuter n ring.inner).length = n ∧
      (IntegerSets.entries (builtOuter n ring.inner)).length = n ∧
      ScalarSet.compare .eq (IntegerSets.entries (builtOuter n ring.inner))
        (ScalarSet.difference (IntegerSets.entries (ints (labels n)))
          (IntegerSets.entries (ints ring.inner))) = true := by
  have constructed := builtOuter_magic ring positive sum magic
  have full : (builtOuter n ring.inner).length = n := by
    rw [constructed, List.length_map, ring.outer_length]
  have distinct : (builtOuter n ring.inner).Nodup := by
    rw [constructed]
    exact List.Pairwise.map (fun value : Nat => (value : Int))
      (fun a b different same => different (Int.ofNat.inj same)) (outer_nodup ring)
  refine ⟨full, ((IntegerSets.entries_length_eq _).mpr distinct).trans full, ?_⟩
  apply (validation_members n ring.inner _).mpr
  intro value
  simpa only [constructed, ints] using ring_complement_ints ring value

end ProjectEulerStatements.MagicRing
