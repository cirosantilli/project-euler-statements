import ProjectEulerStatements.Lib.MagicRing
import Init.Data.List.MinMaxIdx

/-! Canonical rotation starts at the least outer label and preserves every line. -/
namespace ProjectEulerStatements.MagicRing
set_option Elab.async false

def Ring.rotate {n : Nat} (ring : Ring n) (offset : Nat) : Ring n where
  outer := ring.outer.rotate offset
  inner := ring.inner.rotate offset
  outer_length := by simp [ring.outer_length]
  inner_length := by simp [ring.inner_length]
  labels := ((List.rotate_perm ring.outer offset).append
    (List.rotate_perm ring.inner offset)).trans ring.labels

theorem triples_rotate (outer inner next : List Nat) (offset : Nat)
    (same : outer.length = inner.length) (sameNext : outer.length = next.length) :
    triples (outer.rotate offset) (inner.rotate offset) (next.rotate offset) =
      (triples outer inner next).rotate offset := by
  have zipped : (inner.zip next).rotate offset =
      (inner.rotate offset).zip (next.rotate offset) := by
    simpa only [List.zip_eq_zipWith] using
      List.zipWith_rotate_distrib Prod.mk inner next offset (by omega)
  have all := List.zipWith_rotate_distrib (fun (value : Nat) (pair : Nat × Nat) =>
      (value, pair.1, pair.2))
    outer (inner.zip next) offset (by simp [← same, ← sameNext])
  rw [zipped] at all
  exact all.symm

theorem cycle_rotate {n : Nat} (ring : Ring n) (offset : Nat) :
    cycle (ring.rotate offset).outer (ring.rotate offset).inner =
      (cycle ring.outer ring.inner).rotate offset := by
  change triples (ring.outer.rotate offset) (ring.inner.rotate offset)
    ((ring.inner.rotate offset).rotate 1) = _
  have commute : (ring.inner.rotate offset).rotate 1 = (ring.inner.rotate 1).rotate offset := by
    simp only [List.rotate_rotate, Nat.add_comm]
  rw [commute, triples_rotate]
  · rfl
  · rw [ring.outer_length, ring.inner_length]
  · simp [ring.outer_length, ring.inner_length]

theorem magic_rotate_iff {n : Nat} (ring : Ring n) (offset target : Nat) :
    Magic (ring.rotate offset) target ↔ Magic ring target := by
  simp only [Magic, cycle_rotate, List.mem_rotate]

theorem rotate_zero {n : Nat} (ring : Ring n) : ring.rotate 0 = ring := by
  cases ring
  simp [Ring.rotate]

theorem outer_nodup {n : Nat} (ring : Ring n) : ring.outer.Nodup := by
  have distinct := ring.labels.symm.nodup (List.nodup_range' (s := 1) (n := 2 * n))
  exact (List.nodup_append.mp distinct).1

theorem inner_nodup {n : Nat} (ring : Ring n) : ring.inner.Nodup := by
  have distinct := ring.labels.symm.nodup (List.nodup_range' (s := 1) (n := 2 * n))
  exact (List.nodup_append.mp distinct).2.1

def minimumIndex (values : List Nat) : Nat := (values.minIdxOn? id).getD 0

theorem minimumIndex_eq (values : List Nat) (nonempty : values ≠ []) :
    minimumIndex values = values.minIdxOn id nonempty := by
  cases values with
  | nil => contradiction
  | cons first rest => rfl

theorem minimumIndex_inside (values : List Nat) (nonempty : values ≠ []) :
    minimumIndex values < values.length := by
  rw [minimumIndex_eq values nonempty]
  exact List.minIdxOn_lt_length nonempty

theorem minimumIndex_le (values : List Nat) (nonempty : values ≠ []) (value : Nat)
    (member : value ∈ values) :
    values[minimumIndex values]'(minimumIndex_inside values nonempty) ≤ value := by
  have bounded : values[values.minIdxOn id nonempty] ≤ value := by
    rw [List.getElem_minIdxOn]
    exact List.apply_minOn_le_of_mem (f := id) member
  simpa only [minimumIndex_eq values nonempty] using bounded

theorem minimumIndex_unique (values : List Nat) (distinct : values.Nodup) (index : Nat)
    (inside : index < values.length) (least : ∀ value ∈ values, values[index] ≤ value) :
    minimumIndex values = index := by
  have nonempty : values ≠ [] := List.ne_nil_of_mem (List.getElem_mem inside)
  have minimum := minimumIndex_inside values nonempty
  apply (List.getElem_inj distinct).mp
  exact le_antisymm (minimumIndex_le values nonempty _ (List.getElem_mem inside))
    (least _ (List.getElem_mem minimum))

def Canonical {n : Nat} (ring : Ring n) : Prop :=
  ∀ value ∈ ring.outer, ring.outer.headD 0 ≤ value

theorem canonical_rotate {n : Nat} (ring : Ring n) (offset : Nat)
    (inside : offset < ring.outer.length)
    (least : ∀ value ∈ ring.outer, ring.outer[offset] ≤ value) :
    Canonical (ring.rotate offset) := by
  intro value member
  have head : (ring.rotate offset).outer.headD 0 = ring.outer[offset] := by
    change (ring.outer.rotate offset).headD 0 = _
    simp [List.head?_rotate inside, List.getElem?_eq_getElem inside]
  rw [head]
  exact least value (List.mem_rotate.mp member)

def Ring.canonicalize {n : Nat} (ring : Ring n) : Ring n := ring.rotate (minimumIndex ring.outer)

theorem canonicalize_canonical {n : Nat} (ring : Ring n) (positive : 0 < n) :
    Canonical ring.canonicalize := by
  have nonempty : ring.outer ≠ [] := by
    intro empty
    have := ring.outer_length
    rw [empty] at this
    simp at this
    omega
  exact canonical_rotate ring (minimumIndex ring.outer) (minimumIndex_inside ring.outer nonempty)
    (minimumIndex_le ring.outer nonempty)

theorem minimumIndex_zero (values : List Nat) (nonempty : values ≠ [])
    (least : ∀ value ∈ values, values.headD 0 ≤ value) : minimumIndex values = 0 := by
  have same : values.head nonempty = values.headD 0 := by
    cases values with
    | nil => contradiction
    | cons _ _ => rfl
  have selected : values.minIdxOn? id = some 0 := List.minIdxOn?_eq_some_zero_iff.mpr
    ⟨nonempty, by simpa only [id_eq, same] using least⟩
  simp only [minimumIndex, selected, Option.getD_some]

theorem canonicalize_fixed {n : Nat} (ring : Ring n) (positive : 0 < n)
    (canonical : Canonical ring) :
    ring.canonicalize = ring := by
  have nonempty : ring.outer ≠ [] := by
    intro empty
    have := ring.outer_length
    rw [empty] at this
    simp at this
    omega
  rw [Ring.canonicalize, minimumIndex_zero ring.outer nonempty canonical, rotate_zero]

theorem canonicalize_magic {n : Nat} (ring : Ring n) (target : Nat) (magic : Magic ring target) :
    Magic ring.canonicalize target := (magic_rotate_iff ring _ target).mpr magic

theorem rotated_text_length {n : Nat} (ring : Ring n) (offset : Nat) :
    (text (ring.rotate offset).outer (ring.rotate offset).inner).toList.length =
      (text ring.outer ring.inner).toList.length := by
  rw [text_length, text_length]
  exact congrArg (fun sum => ((List.range' 1 (2 * n)).map digitWidth).sum + sum)
    (((List.rotate_perm ring.inner offset).map digitWidth).sum_eq)

end ProjectEulerStatements.MagicRing
