import ProjectEulerStatements.Lib.QuadraticPrimes
import ProjectEulerStatements.Lib.QuadraticPrimeCertificate
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-! Every canonical prime run reaching 71 terms has the same coefficient pair. -/
namespace ProjectEulerStatements.QuadraticPrimeWinner
open P27 QuadraticPrimes QuadraticPrimeCertificate

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000


private theorem survives_of_prime (value : Int) (prime : isPrimeInt value = true) :
    survives value = true := by
  obtain ⟨positive, primeNat⟩ := prime_iff value |>.mp prime
  change (_ && _) = true
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by simpa using positive, List.all_eq_true.mpr ?_⟩
  intro divisor member
  have large : 1 < divisor := by
    simp only [smallPrimes, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  apply decide_eq_true_iff.mpr
  by_cases same : value = divisor
  · exact Or.inl same
  · right
    intro divides
    have dvdInt : divisor ∣ value := Int.dvd_of_emod_eq_zero divides
    have castValue : (value.toNat : Int) = value := Int.toNat_of_nonneg (by omega)
    have castDivisor : (divisor.toNat : Int) = divisor := Int.toNat_of_nonneg (by omega)
    have dvdNat : divisor.toNat ∣ value.toNat := Int.natCast_dvd_natCast.mp (by simpa only [castValue, castDivisor] using dvdInt)
    exact Nat.not_prime_of_dvd_of_ne dvdNat (by omega) (by intro equal; apply same; omega) primeNat

private theorem retained (indices : List Nat) (pairs : List (Int × Int)) (a b : Int)
    (member : (a, b) ∈ pairs)
    (prime : ∀ n ∈ indices, isPrimeInt (quad a b n) = true) :
    (a, b) ∈ indices.foldl (fun pairs n => pairs.filter (fun p => survives (quad p.1 p.2 n))) pairs := by
  induction indices generalizing pairs with
  | nil => exact member
  | cons n rest ih =>
      apply ih
      · exact List.mem_filter.mpr ⟨member, survives_of_prime _ (prime n (by simp))⟩
      · intro k hk
        exact prime k (by simp [hk])

private theorem candidate_member (a b : Int) (lowerA : -63 ≤ a) (upperA : a ≤ 999)
    (lowerB : 71 ≤ b) (upperB : b ≤ 1000) (oddA : a % 2 = 1)
    (primeB : isPrimeInt b = true) : (a, b) ∈ candidates := by
  let bi := (b - 71).toNat
  let ai := ((a + 63) / 2).toNat
  have biBound : bi < 930 := by dsimp [bi]; omega
  have aiBound : ai < 532 := by dsimp [ai]; omega
  have bValue : (71 : Int) + bi = b := by dsimp [bi]; omega
  have aValue : (-63 : Int) + 2 * ai = a := by dsimp [ai]; omega
  change (a, b) ∈ eligibleBs.flatMap row
  apply List.mem_flatMap.mpr
  refine ⟨b, List.mem_filter.mpr ⟨?_, survives_of_prime b primeB⟩, ?_⟩
  · exact List.mem_map.mpr ⟨bi, List.mem_range.mpr biBound, bValue⟩
  · exact List.mem_map.mpr ⟨ai, List.mem_range.mpr aiBound, by simp [aValue]⟩

/-- The canonical pair produces exactly seventy-one primes before its first composite. -/
theorem canonical_length : consecPrimeLen (-61) 971 = 71 := by
  rw [consecPrimeLen_eq_first]
  have failure : isPrimeInt (quad (-61) 971 71) = false := by norm_num [quad, isPrimeInt, Int.toNat]
  have upper := first_le (-61) 971 71 failure
  have primePrefix : ∀ n : Nat, n < 71 → isPrimeInt (quad (-61) 971 n) = true := by
    intro n bound
    interval_cases n <;> norm_num [quad, isPrimeInt, Int.toNat]
  have lower : 71 ≤ first (-61) 971 := by
    by_contra small
    have accepted := primePrefix (first (-61) 971) (by omega)
    have rejected := first_spec (-61) 971
    have impossible : false = true := rejected.symm.trans accepted
    cases impossible
  omega

private theorem failure_bound (a b : Int) (n : Nat) (small : n < 71)
    (failure : isPrimeInt (quad a b n) = false) : consecPrimeLen a b < 71 := by
  rw [consecPrimeLen_eq_first]
  exact (first_le a b n failure).trans_lt small

/-- Any run at least as long as the canonical one must be that same pair. -/
theorem unique_long (a b : Int) (upperA : a ≤ 999) (upperB : b ≤ 1000)
    (long : 71 ≤ consecPrimeLen a b) : a = -61 ∧ b = 971 := by
  have largeFirst : 71 ≤ first a b := by simpa only [consecPrimeLen_eq_first] using long
  have primePrefix : ∀ n : Nat, n < 71 → isPrimeInt (quad a b n) = true :=
    fun n hn => before_first a b n (by omega)
  have primeB : isPrimeInt b = true := by simpa [quad] using primePrefix 0 (by omega)
  have bPositive := ((prime_iff b).mp primeB).1
  have lowerB : 71 ≤ b := by
    have bound := first_lt_bound a b
    have cast := Int.natAbs_of_nonneg (by omega : 0 ≤ b)
    simp only [consecPrimeBound] at bound
    omega
  have lowerA : -63 ≤ a := by
    have positive := ((prime_iff _).mp (primePrefix 32 (by omega))).1
    norm_num [quad] at positive
    omega
  have oddA : a % 2 = 1 := by
    by_cases even : a % 2 = 0
    · have short := odd_b_even_a a b primeB (by omega) even
      omega
    · omega
  have member : (a, b) ∈ remaining := by
    obtain ⟨rowB, admissibleB, inRow⟩ := List.mem_flatMap.mp
      (candidate_member a b lowerA upperA lowerB upperB oddA primeB)
    exact List.mem_flatMap.mpr ⟨rowB, admissibleB,
      retained (List.range' 1 70) (row rowB) a b inRow
        (by intro n hn; have := List.mem_range'.mp hn; apply primePrefix n; omega)⟩
  rw [remaining_checked] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair | pair
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (463) 83 9 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (273) 109 11 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (801) 127 14 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (475) 137 5 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (825) 223 8 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (601) 227 6 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (725) 293 8 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (415) 317 15 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (629) 347 11 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (275) 383 10 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (477) 409 3 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (783) 433 7 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (465) 547 8 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (721) 557 5 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (477) 613 4 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (277) 659 9 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (991) 677 7 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (925) 683 2 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (417) 733 14 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (603) 829 5 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (479) 887 2 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (803) 929 13 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (279) 937 8 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    exact ⟨rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (631) 977 10 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega
  · obtain ⟨rfl, rfl⟩ := pair
    have short := failure_bound (923) 983 6 (by decide) (by norm_num [quad, isPrimeInt, Int.toNat])
    omega

/-- All pairs in the canonical search rectangle have score at most seventy-one. -/
theorem score_le (a b : Int) (upperA : a ≤ 999) (upperB : b ≤ 1000) :
    consecPrimeLen a b ≤ 71 := by
  by_cases long : 71 ≤ consecPrimeLen a b
  · obtain ⟨rfl, rfl⟩ := unique_long a b upperA upperB long
    rw [canonical_length]
  · omega

end ProjectEulerStatements.QuadraticPrimeWinner
