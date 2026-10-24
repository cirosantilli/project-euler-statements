import ProjectEulerStatements.Lib.CircularPrimes
import Mathlib.Logic.Function.Iterate

namespace ProjectEulerStatements.CircularPrimes

set_option Elab.async false

theorem digitsBE_nonempty (n : Nat) (positive : 0 < n) : P35.digitsBE n ≠ [] := by
  intro empty
  have zero := digitsToNat_digitsBE n
  rw [empty] at zero
  change 0 = n at zero
  omega

theorem iterate_rotateValue_digits (digits : List Nat) (nonempty : digits ≠ [])
    (bounds : ∀ digit ∈ digits, digit < 10) (index : Nat) :
    (rotateValue digits.length)^[index] (P35.digitsToNat digits) =
      P35.digitsToNat (digits.rotate index) := by
  induction index with
  | zero => simp
  | succ index ih =>
      rw [Function.iterate_succ_apply', ih]
      have rotated : digits.rotate index ≠ [] := by simpa using nonempty
      simpa only [List.length_rotate, List.rotate_rotate] using
        rotateValue_digits (digits.rotate index) rotated
          (fun digit member => bounds digit (List.mem_rotate.mp member))

/-- The actual arithmetic rotation loop, including rotations with leading zeros,
enumerates the same fixed-width digit rotations as the reference definition. -/
theorem arithmetic_rotations (n : Nat) (positive : 0 < n) :
    (List.range (P35.digitsBE n).length).map
      (fun index => (rotateValue (P35.digitsBE n).length)^[index] n) = rotationValues n := by
  rw [rotationValues, rotations_eq_map_rotate, List.map_map]
  apply List.map_congr_left
  intro index _
  simpa only [digitsToNat_digitsBE, Function.comp_apply] using
    iterate_rotateValue_digits (P35.digitsBE n) (digitsBE_nonempty n positive)
      (digitsBE_bounds n) index

def AllPrimeRotations (digits : List Nat) : Prop :=
  ∀ index, Nat.Prime (P35.digitsToNat (digits.rotate index))

theorem allPrimeRotations_first {digits : List Nat} (prime : AllPrimeRotations digits) :
    Nat.Prime (P35.digitsToNat digits) := by simpa using prime 0

theorem allPrimeRotations_rotate {digits : List Nat} (prime : AllPrimeRotations digits)
    (index : Nat) :
    AllPrimeRotations (digits.rotate index) := by
  intro other
  simpa only [List.rotate_rotate] using prime (index + other)

theorem allPrimeRotations_of_isRotated {digits other : List Nat}
    (prime : AllPrimeRotations digits) (rotated : List.IsRotated digits other) :
    AllPrimeRotations other := by
  obtain ⟨index, rfl⟩ := rotated
  exact allPrimeRotations_rotate prime index

theorem circular_iff (n : Nat) :
    P35.isCircularPrime n = true ↔ 2 ≤ n ∧
      ∀ digits ∈ P35.rotations (P35.digitsBE n), Nat.Prime (P35.digitsToNat digits) := by
  by_cases small : n < 2
  · simp [P35.isCircularPrime, small, show ¬ 2 ≤ n by omega]
  · simp [P35.isCircularPrime, small, show 2 ≤ n by omega,
      listAll_map_eq_all, P35.isPrime, List.all_eq_true]

theorem circular_allPrimeRotations (n : Nat) (circular : P35.isCircularPrime n = true) :
    AllPrimeRotations (P35.digitsBE n) := by
  obtain ⟨lower, prime⟩ := (circular_iff n).mp circular
  have nonempty := digitsBE_nonempty n (by omega)
  have length : 0 < (P35.digitsBE n).length := List.length_pos_of_ne_nil nonempty
  intro index
  apply prime
  rw [rotations_eq_map_rotate]
  refine List.mem_map.mpr ⟨index % (P35.digitsBE n).length,
    List.mem_range.mpr (Nat.mod_lt _ length), ?_⟩
  exact List.rotate_mod _ _

/-- A multi-digit all-prime cycle cannot contain a one-digit value: the next
fixed-width rotation would append zero, producing a multiple of ten. -/
theorem allPrimeRotations_ge_ten (digits : List Nat) (long : 2 ≤ digits.length)
    (bounds : ∀ digit ∈ digits, digit < 10) (prime : AllPrimeRotations digits) :
    10 ≤ P35.digitsToNat digits := by
  have first := (allPrimeRotations_first prime).two_le
  by_contra notLarge
  have small : P35.digitsToNat digits < 10 := by omega
  have place : 10 ≤ 10 ^ (digits.length - 1) := by
    calc
      10 = 10 ^ 1 := by decide
      _ ≤ 10 ^ (digits.length - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have fits : P35.digitsToNat digits < 10 ^ (digits.length - 1) := by omega
  have nonempty : digits ≠ [] := by intro empty; simp [empty] at long
  have next := prime 1
  rw [← rotateValue_digits digits nonempty bounds] at next
  simp only [rotateValue, Nat.mod_eq_of_lt fits, Nat.div_eq_of_lt fits, Nat.add_zero] at next
  have divides : 10 ∣ P35.digitsToNat digits * 10 := ⟨P35.digitsToNat digits, Nat.mul_comm _ _⟩
  have forced := (Nat.dvd_prime next).mp divides
  omega

theorem prime_last_digit (n : Nat) (large : 10 ≤ n) (prime : Nat.Prime n) :
    n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9 := by
  have notFive : n % 10 ≠ 5 := by
    intro five
    have divisible : 5 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
    have forced := (Nat.dvd_prime prime).mp divisible
    omega
  rcases prime.eq_two_or_odd with two | odd <;> omega

def AllowedDigits (digits : List Nat) : Prop :=
  ∀ digit ∈ digits, digit = 1 ∨ digit = 3 ∨ digit = 7 ∨ digit = 9

theorem allPrimeRotations_allowed (digits : List Nat) (long : 2 ≤ digits.length)
    (bounds : ∀ digit ∈ digits, digit < 10) (prime : AllPrimeRotations digits) :
    AllowedDigits digits := by
  intro digit member
  have digitBound := bounds digit member
  obtain ⟨front, back, rfl⟩ := List.append_of_mem member
  let other := (back ++ front) ++ [digit]
  have rotated : List.IsRotated (front ++ digit :: back) other := by
    refine ⟨(front ++ [digit]).length, ?_⟩
    have regroup : front ++ digit :: back = (front ++ [digit]) ++ back := by simp
    rw [regroup, List.rotate_append_length_eq]
    simp [other, List.append_assoc]
  have otherPrime := allPrimeRotations_of_isRotated prime rotated
  have otherLong : 2 ≤ other.length := by simpa only [← rotated.perm.length_eq] using long
  have otherBounds : ∀ d ∈ other, d < 10 := fun d member => bounds d (rotated.mem_iff.mpr member)
  have last := prime_last_digit (P35.digitsToNat other)
    (allPrimeRotations_ge_ten other otherLong otherBounds otherPrime)
    (allPrimeRotations_first otherPrime)
  have remainder : P35.digitsToNat other % 10 = digit := by
    change P35.digitsToNat ((back ++ front) ++ [digit]) % 10 = digit
    rw [digitsToNat_append_singleton]
    simp [Nat.add_mod, Nat.mod_eq_of_lt digitBound]
  simpa only [remainder] using last

theorem circular_allowed (n : Nat) (large : 10 ≤ n) (circular : P35.isCircularPrime n = true) :
    AllowedDigits (P35.digitsBE n) := by
  have below := digitsToNat_lt (P35.digitsBE n) (digitsBE_bounds n)
  rw [digitsToNat_digitsBE] at below
  have long : 2 ≤ (P35.digitsBE n).length := by
    by_contra short
    have alternatives : (P35.digitsBE n).length = 0 ∨ (P35.digitsBE n).length = 1 := by omega
    rcases alternatives with length | length <;> simp [length] at below <;> omega
  exact allPrimeRotations_allowed _ long (digitsBE_bounds n) (circular_allPrimeRotations n circular)

end ProjectEulerStatements.CircularPrimes
