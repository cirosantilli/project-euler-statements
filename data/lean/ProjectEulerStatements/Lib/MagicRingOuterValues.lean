import ProjectEulerStatements.Lib.MagicRingCandidates
import ProjectEulerStatements.Lib.MagicRingOuterCalls

/-! Successful signed outer-label construction is exactly the natural forced-outer model. -/
namespace ProjectEulerStatements.MagicRing
open MagicRingOuterCalls (forcedValue outerPrefix)
set_option Elab.async false

def builtOuter (n : Nat) (inner : List Nat) : List Int :=
  outerPrefix n inner (target n inner) 0

theorem forcedValue_toNat (n : Nat) (inner : List Nat) (index : Nat) :
    (forcedValue n inner (target n inner) index).toNat =
      target n inner - (inner[index]?).getD 0 - (inner[(index + 1) % n]?).getD 0 := by
  simp [forcedValue]

theorem builtOuter_length (n : Nat) (inner : List Nat) : (builtOuter n inner).length ≤ n := by
  simpa only [builtOuter, Nat.sub_zero] using
    MagicRingOuterCalls.prefix_length n inner (target n inner) 0

theorem builtOuter_valid (n : Nat) (inner : List Nat) (value : Int)
    (member : value ∈ builtOuter n inner) : 1 ≤ value ∧ value ≤ 2 * (n : Int) :=
  MagicRingOuterCalls.prefix_valid n inner (target n inner) 0 value member

theorem builtOuter_toNat (n : Nat) (inner : List Nat)
    (full : (builtOuter n inner).length = n) :
    (builtOuter n inner).map Int.toNat = derivedOuter n inner := by
  have complete := MagicRingOuterCalls.prefix_full n inner (target n inner) 0
    (by simpa only [Nat.sub_zero] using full)
  rw [show builtOuter n inner = _ from complete]
  simp only [Nat.sub_zero, ← List.range_eq_range', List.map_map]
  exact List.map_congr_left (fun index _ => forcedValue_toNat n inner index)

theorem builtOuter_cast (n : Nat) (inner : List Nat)
    (full : (builtOuter n inner).length = n) :
    builtOuter n inner = (derivedOuter n inner).map (fun value : Nat => (value : Int)) := by
  have roundtrip : ((builtOuter n inner).map Int.toNat).map (fun value : Nat => (value : Int)) =
      builtOuter n inner := by
    rw [List.map_map]
    calc
      _ = (builtOuter n inner).map id := List.map_congr_left (by
        intro value member
        exact Int.toNat_of_nonneg (by have := (builtOuter_valid n inner value member).1; omega))
      _ = _ := List.map_id _
  rw [builtOuter_toNat n inner full] at roundtrip
  exact roundtrip.symm

theorem builtOuter_pack (n : Nat) (inner : List Nat) (size : inner.length = n)
    (innerDistinct : inner.Nodup) (innerSubset : ∀ value ∈ inner, value ∈ labels n)
    (full : (builtOuter n inner).length = n) (outerDistinct : (builtOuter n inner).Nodup)
    (complement : ∀ value : Int, value ∈ builtOuter n inner ↔
      value ∈ (labels n).map (fun item : Nat => (item : Int)) ∧
      value ∉ inner.map (fun item : Nat => (item : Int))) :
    ∃ ring : Ring n, ring.inner = inner ∧
      builtOuter n inner = ring.outer.map (fun value : Nat => (value : Int)) ∧
      ring.outer = derivedOuter n ring.inner := by
  let outer := derivedOuter n inner
  have castOuter : builtOuter n inner = outer.map (fun value : Nat => (value : Int)) :=
    builtOuter_cast n inner full
  have distinct : outer.Nodup :=
    List.Nodup.of_map (fun value : Nat => (value : Int)) (castOuter ▸ outerDistinct)
  have complete : ∀ value, value ∈ outer ↔ value ∈ labels n ∧ value ∉ inner := by
    intro value
    simpa only [castOuter, List.mem_map, Int.natCast_inj, exists_eq_right] using complement value
  let ring : Ring n := ⟨outer, inner, derivedOuter_length n inner, size,
    perm_of_complement n outer inner distinct innerDistinct innerSubset complete⟩
  exact ⟨ring, rfl, castOuter, rfl⟩

theorem builtOuter_magic {n : Nat} (ring : Ring n) (positive : 0 < n)
    (sum : Nat) (magic : Magic ring sum) :
    builtOuter n ring.inner = ring.outer.map (fun value : Nat => (value : Int)) := by
  have reconstructed := derivedOuter_eq ring positive sum magic
  have value_eq (index : Nat) (inside : index < n) :
      forcedValue n ring.inner (target n ring.inner) index =
        (ring.outer[index]'(by rw [ring.outer_length]; exact inside) : Int) := by
    have inRange : index < (List.range n).length := by simpa using inside
    have inOuter : index < ring.outer.length := by rw [ring.outer_length]; exact inside
    have same := congrArg (fun values => values[index]?) reconstructed
    simp only [derivedOuter, List.getElem?_map, List.getElem?_eq_getElem inRange,
      List.getElem_range, Option.map_some, List.getElem?_eq_getElem inOuter,
      Option.some.injEq] at same
    have forced := forcedValue_toNat n ring.inner index
    have bounds := label_bounds ring ring.outer[index] (Or.inl (List.getElem_mem inOuter))
    omega
  have full : (builtOuter n ring.inner).length = n := by
    apply (MagicRingOuterCalls.prefix_complete_iff n ring.inner (target n ring.inner) 0).mpr
    intro index member
    have bound := List.mem_range'_1.mp member
    have inside : index < n := by omega
    rw [value_eq index inside]
    have inOuter : index < ring.outer.length := by rw [ring.outer_length]; exact inside
    have bounds := label_bounds ring (ring.outer[index]'inOuter)
      (Or.inl (List.getElem_mem inOuter))
    unfold MagicRingOuterCalls.valid
    exact_mod_cast bounds
  rw [builtOuter_cast n ring.inner full, reconstructed]

end ProjectEulerStatements.MagicRing
