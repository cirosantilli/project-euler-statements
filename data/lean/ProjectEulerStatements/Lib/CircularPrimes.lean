import ProjectEulerStatements.P35
import Mathlib.Data.List.Rotate
import Mathlib.Data.Finset.Card
import Init.Data.List.Nat.Range
import Lean.Elab.Tactic.Omega

/-! Decimal rotations and counting interfaces shared by the two circular-prime
implementations. All statements apply to arbitrary inputs and bounds. -/
namespace ProjectEulerStatements.CircularPrimes

set_option Elab.async false

private theorem fold_and (items : List Bool) (initial : Bool) :
    items.foldl (fun before item => before && item) initial = (initial && items.all id) := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih => simp [List.foldl, ih, Bool.and_assoc]

theorem listAll_eq_all (items : List Bool) : P35.listAll items = items.all id := by
  simp [P35.listAll, fold_and]

theorem listAll_map_eq_all (items : List α) (predicate : α → Bool) :
    P35.listAll (items.map predicate) = items.all predicate := by
  simp [listAll_eq_all, List.all_map]

theorem fold_count (items : List α) (predicate : α → Bool) (initial : Nat) :
    items.foldl (fun total item => if predicate item then total + 1 else total) initial =
      initial + (items.filter predicate).length := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
      cases selected : predicate head <;>
        simp [List.foldl, List.filter, selected, ih]; omega

theorem naive_filter_length (limit : Nat) :
    P35.naive limit = ((List.range limit).filter P35.isCircularPrime).length := by
  have same : ((List.range limit).filter P35.isCircularPrime).toFinset =
      (Finset.range limit).filter (fun n => P35.isCircularPrime n) := by
    ext n
    simp
  change ((Finset.range limit).filter (fun n => P35.isCircularPrime n)).card = _
  rw [← same]
  exact List.toFinset_card_of_nodup (List.Nodup.filter P35.isCircularPrime List.nodup_range)

theorem naive_fold (limit : Nat) :
    P35.naive limit = (List.range limit).foldl
      (fun total n => if P35.isCircularPrime n then total + 1 else total) 0 := by
  simp [naive_filter_length, fold_count]

@[simp] theorem digitsToNat_digitsBE (n : Nat) :
    P35.digitsToNat (P35.digitsBE n) = n := by
  simp [P35.digitsToNat, P35.digitsBE, Nat.ofDigits_digits]

theorem digitsBE_bounds (n digit : Nat) (member : digit ∈ P35.digitsBE n) : digit < 10 := by
  apply Nat.digits_lt_base (by decide : 1 < 10)
  simpa [P35.digitsBE] using member

theorem rotations_eq_map_rotate (digits : List Nat) :
    P35.rotations digits = (List.range digits.length).map digits.rotate := by
  unfold P35.rotations
  apply List.map_congr_left
  intro index member
  exact (List.rotate_eq_drop_append_take (Nat.le_of_lt (List.mem_range.mp member))).symm

theorem rotation_length (digits rotation : List Nat) (member : rotation ∈ P35.rotations digits) :
    rotation.length = digits.length := by
  rw [rotations_eq_map_rotate] at member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact List.length_rotate _ _

theorem rotation_members (digits rotation : List Nat) (member : rotation ∈ P35.rotations digits) :
    ∀ digit, digit ∈ rotation ↔ digit ∈ digits := by
  rw [rotations_eq_map_rotate] at member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact fun _ => List.mem_rotate

theorem digitsToNat_lt (digits : List Nat) (bounds : ∀ digit ∈ digits, digit < 10) :
    P35.digitsToNat digits < 10 ^ digits.length := by
  simpa [P35.digitsToNat] using
    Nat.ofDigits_lt_base_pow_length (by decide : 1 < 10)
      (fun digit member => bounds digit (List.mem_reverse.mp member))

def rotationValues (n : Nat) : List Nat :=
  (P35.rotations (P35.digitsBE n)).map P35.digitsToNat

theorem rotationValues_bound (n rotation : Nat) (member : rotation ∈ rotationValues n) :
    rotation < 10 ^ (P35.digitsBE n).length := by
  obtain ⟨digits, rotated, rfl⟩ := List.mem_map.mp member
  rw [← rotation_length _ _ rotated]
  exact digitsToNat_lt digits (fun digit present =>
    digitsBE_bounds n digit ((rotation_members _ _ rotated digit).mp present))

/-- Keep the original width even when a rotation begins with zero. -/
def rotateValue (width value : Nat) : Nat :=
  (value % 10 ^ (width - 1)) * 10 + value / 10 ^ (width - 1)

theorem digitsToNat_cons (head : Nat) (tail : List Nat) :
    P35.digitsToNat (head :: tail) = P35.digitsToNat tail + 10 ^ tail.length * head := by
  simp [P35.digitsToNat, Nat.ofDigits_append, Nat.ofDigits]

theorem digitsToNat_append_singleton (head : Nat) (tail : List Nat) :
    P35.digitsToNat (tail ++ [head]) = P35.digitsToNat tail * 10 + head := by
  simp [P35.digitsToNat, Nat.ofDigits, Nat.add_comm, Nat.mul_comm]

theorem rotateValue_digits (digits : List Nat) (nonempty : digits ≠ [])
    (bounds : ∀ digit ∈ digits, digit < 10) :
    rotateValue digits.length (P35.digitsToNat digits) = P35.digitsToNat (digits.rotate 1) := by
  cases digits with
  | nil => exact (nonempty rfl).elim
  | cons head tail =>
      have small := digitsToNat_lt tail (fun digit member => bounds digit (by simp [member]))
      have positive : 0 < 10 ^ tail.length := Nat.pow_pos (by decide)
      simp only [rotateValue, List.length_cons, Nat.add_sub_cancel, digitsToNat_cons,
        Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ positive,
        Nat.mod_eq_of_lt small, Nat.div_eq_of_lt small, Nat.zero_add]
      simpa using (digitsToNat_append_singleton head tail).symm

end ProjectEulerStatements.CircularPrimes
