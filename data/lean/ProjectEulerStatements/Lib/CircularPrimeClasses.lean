import ProjectEulerStatements.Lib.CircularPrimeStrings

namespace ProjectEulerStatements.CircularPrimes

set_option Elab.async false

instance (digits : List Nat) : Decidable (AllowedDigits digits) := by
  unfold AllowedDigits
  infer_instance

theorem allowed_rotate {digits : List Nat} (allowed : AllowedDigits digits) (index : Nat) :
    AllowedDigits (digits.rotate index) :=
  fun digit member => allowed digit (List.mem_rotate.mp member)

/-- Allowed digits have no leading zero, including after any rotation. -/
theorem digitsBE_value_of_allowed (digits : List Nat) (allowed : AllowedDigits digits) :
    P35.digitsBE (P35.digitsToNat digits) = digits := by
  have bounds : ∀ digit ∈ digits.reverse, digit < 10 := by
    intro digit member
    rcases allowed digit (List.mem_reverse.mp member) with rfl | rfl | rfl | rfl <;> decide
  have last : ∀ nonempty : digits.reverse ≠ [], digits.reverse.getLast nonempty ≠ 0 := by
    intro nonempty
    have member := List.mem_reverse.mp (List.getLast_mem nonempty)
    rcases allowed _ member with value | value | value | value <;> rw [value] <;> decide
  simp only [P35.digitsBE, P35.digitsToNat]
  rw [Nat.digits_ofDigits 10 (by decide) _ bounds last, List.reverse_reverse]

theorem value_pos_of_allowed (digits : List Nat) (nonempty : digits ≠ [])
    (allowed : AllowedDigits digits) :
    0 < P35.digitsToNat digits := by
  apply Nat.pos_of_ne_zero
  intro zero
  have recovered := digitsBE_value_of_allowed digits allowed
  rw [zero] at recovered
  exact nonempty (by simpa [P35.digitsBE] using recovered.symm)

def orbit (n : Nat) : Finset Nat := (rotationValues n).toFinset

theorem mem_orbit_iff (n : Nat) (positive : 0 < n) (value : Nat) :
    value ∈ orbit n ↔ ∃ index, P35.digitsToNat ((P35.digitsBE n).rotate index) = value := by
  constructor
  · intro member
    obtain ⟨digits, rotated, valueEq⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    rw [rotations_eq_map_rotate] at rotated
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp rotated
    exact ⟨index, valueEq⟩
  · rintro ⟨index, valueEq⟩
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨(P35.digitsBE n).rotate index, ?_, valueEq⟩
    rw [rotations_eq_map_rotate]
    have length := List.length_pos_of_ne_nil (digitsBE_nonempty n positive)
    exact List.mem_map.mpr ⟨index % (P35.digitsBE n).length,
      List.mem_range.mpr (Nat.mod_lt _ length), List.rotate_mod _ _⟩

theorem mem_orbit_self (n : Nat) (positive : 0 < n) : n ∈ orbit n := by
  apply (mem_orbit_iff n positive n).mpr
  exact ⟨0, by simp⟩

theorem orbit_eq_of_isRotated (n other : Nat) (positive : 0 < n) (otherPositive : 0 < other)
    (rotated : List.IsRotated (P35.digitsBE n) (P35.digitsBE other)) :
    orbit n = orbit other := by
  ext value
  rw [mem_orbit_iff n positive, mem_orbit_iff other otherPositive]
  constructor
  · rintro ⟨index, valueEq⟩
    obtain ⟨back, backEq⟩ := rotated.symm
    refine ⟨back + index, ?_⟩
    rw [← List.rotate_rotate, backEq]
    exact valueEq
  · rintro ⟨index, valueEq⟩
    obtain ⟨forward, forwardEq⟩ := rotated
    refine ⟨forward + index, ?_⟩
    rw [← List.rotate_rotate, forwardEq]
    exact valueEq

theorem orbit_member_digits (n other : Nat) (positive : 0 < n)
    (allowed : AllowedDigits (P35.digitsBE n)) (member : other ∈ orbit n) :
    0 < other ∧ AllowedDigits (P35.digitsBE other) ∧
      List.IsRotated (P35.digitsBE n) (P35.digitsBE other) := by
  obtain ⟨index, rfl⟩ := (mem_orbit_iff n positive other).mp member
  have nonempty : (P35.digitsBE n).rotate index ≠ [] := by
    simpa using digitsBE_nonempty n positive
  have rotatedAllowed := allowed_rotate allowed index
  have recovered := digitsBE_value_of_allowed _ rotatedAllowed
  refine ⟨value_pos_of_allowed _ nonempty rotatedAllowed, ?_, ?_⟩
  · rwa [recovered]
  · exact ⟨index, recovered.symm⟩

theorem orbit_eq_of_mem (n other : Nat) (positive : 0 < n)
    (allowed : AllowedDigits (P35.digitsBE n)) (member : other ∈ orbit n) :
    orbit other = orbit n := by
  obtain ⟨otherPositive, _, rotated⟩ := orbit_member_digits n other positive allowed member
  exact (orbit_eq_of_isRotated n other positive otherPositive rotated).symm

theorem circular_of_allPrimeRotations (n : Nat) (lower : 2 ≤ n)
    (prime : AllPrimeRotations (P35.digitsBE n)) : P35.isCircularPrime n = true := by
  apply (circular_iff n).mpr
  refine ⟨lower, ?_⟩
  intro digits member
  rw [rotations_eq_map_rotate] at member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact prime index

theorem orbit_member_large (n other : Nat) (large : 10 ≤ n)
    (allowed : AllowedDigits (P35.digitsBE n)) (member : other ∈ orbit n) : 10 ≤ other := by
  obtain ⟨_, _, rotated⟩ := orbit_member_digits n other (by omega) allowed member
  apply (digitsBE_length_ge_two other).mp
  rw [← rotated.perm.length_eq]
  exact (digitsBE_length_ge_two n).mpr large

theorem orbit_circular_iff (n other : Nat) (large : 10 ≤ n)
    (allowed : AllowedDigits (P35.digitsBE n)) (member : other ∈ orbit n) :
    P35.isCircularPrime other = true ↔ P35.isCircularPrime n = true := by
  obtain ⟨_, _, rotated⟩ := orbit_member_digits n other (by omega) allowed member
  have otherLarge := orbit_member_large n other large allowed member
  constructor
  · intro circular
    exact circular_of_allPrimeRotations n (by omega)
      (allPrimeRotations_of_isRotated (circular_allPrimeRotations other circular) rotated.symm)
  · intro circular
    exact circular_of_allPrimeRotations other (by omega)
      (allPrimeRotations_of_isRotated (circular_allPrimeRotations n circular) rotated)

end ProjectEulerStatements.CircularPrimes
