import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.NormNum.Prime

namespace ProjectEulerStatements.P51

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

/-- Replace all digits at indices `idxs` (0 = least significant) by digit `d`. -/
def replaceAt (digits : List Nat) (idxs : List Nat) (d : Nat) : List Nat :=
  let rec go (ds : List Nat) (i : Nat) : List Nat :=
    match ds with
    | [] => []
    | x :: xs =>
        let x' := if i ∈ idxs then d else x
        x' :: go xs (i + 1)
  go digits 0

/-- All numbers produced by replacing positions `idxs` with the same digit. -/
def familyNumbers (n : Nat) (idxs : List Nat) : List Nat :=
  let digits := Nat.digits 10 n
  let len := digits.length
  (List.range 10).filterMap (fun d =>
    let ds' := replaceAt digits idxs d
    let m := Nat.ofDigits 10 ds'
    if (Nat.digits 10 m).length = len then
      some m
    else
      none)

/-- Count primes in the replacement family for `n` and index set `idxs`. -/
def primeFamilySize (n : Nat) (idxs : List Nat) : Nat :=
  (familyNumbers n idxs).filter (fun m => isPrime m) |>.length

/-- Whether `n` belongs to a prime family of size at least `k`. -/
def hasPrimeFamily (k n : Nat) : Bool :=
  let digits := Nat.digits 10 n
  let idxs := (List.range digits.length).sublists.filter (fun s => s ≠ [])
  (idxs.any (fun s =>
    decide (n ∈ familyNumbers n s) && decide (primeFamilySize n s ≥ k))) && isPrime n

/-- Ten replacement digits give at most ten family members. -/
theorem primeFamilySize_le_ten (n : Nat) (indices : List Nat) : primeFamilySize n indices ≤ 10 := by
  unfold primeFamilySize familyNumbers
  exact (List.length_filter_le _ _).trans
    ((List.length_filterMap_le _ _).trans_eq (List.length_range (n := 10)))

/-- Thresholds larger than the replacement alphabet cannot be met. -/
theorem no_prime_family_above_ten (k n : Nat) (large : 10 < k) : hasPrimeFamily k n = false := by
  apply Bool.eq_false_iff.mpr
  intro family
  simp only [hasPrimeFamily, Bool.and_eq_true] at family
  obtain ⟨indices, _, accepted⟩ := List.any_eq_true.mp family.1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
  have bound := primeFamilySize_le_ten n indices
  omega

/-- The least qualifying prime, with zero representing absence of a qualifying family. -/
noncomputable def naive (k : Nat) : Nat := by
  classical
  exact if success : ∃ n, hasPrimeFamily k n = true then Nat.find success else 0

example : primeFamilySize 13 [1] = 6 := by
  native_decide

example : primeFamilySize 56003 [1, 2] = 7 := by
  native_decide

example : 120383 ∉ familyNumbers 120383 [1, 3, 5] := by
  decide +kernel

theorem has_eight_prime_family : hasPrimeFamily 8 121313 = true := by
  have family : familyNumbers 121313 [1, 3, 5] =
      [121313, 222323, 323333, 424343, 525353, 626363, 727373, 828383, 929393] := by
    decide +kernel
  have score : 8 ≤ primeFamilySize 121313 [1, 3, 5] := by
    rw [primeFamilySize, family]
    norm_num [isPrime]
  simp only [hasPrimeFamily, Bool.and_eq_true]
  refine ⟨List.any_eq_true.mpr ?_, ?_⟩
  · refine ⟨[1, 3, 5], ?_, ?_⟩
    · decide +kernel
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by simp [family], score⟩
  · norm_num [isPrime]

/-- The checked eight-member family also witnesses every smaller requested threshold. -/
theorem exists_prime_family (k : Nat) (bound : k ≤ 8) : ∃ n, hasPrimeFamily k n = true := by
  have eight := has_eight_prime_family
  simp only [hasPrimeFamily, Bool.and_eq_true] at eight
  obtain ⟨indices, member, accepted⟩ := List.any_eq_true.mp eight.1
  refine ⟨121313, ?_⟩
  simp only [hasPrimeFamily, Bool.and_eq_true]
  refine ⟨List.any_eq_true.mpr ⟨indices, member, ?_⟩, eight.2⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted ⊢
  exact ⟨accepted.1, bound.trans accepted.2⟩

end ProjectEulerStatements.P51
