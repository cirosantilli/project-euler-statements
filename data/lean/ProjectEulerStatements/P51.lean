import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Digits.Defs

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
  (idxs.any (fun s => decide (primeFamilySize n s ≥ k))) && isPrime n

/-- Existence of a prime family of size `k`. -/
theorem exists_prime_family (k : Nat) : ∃ n, hasPrimeFamily k n = true := by
  sorry

/-- Smallest prime that is part of a `k`-prime replacement family. -/
def naive (k : Nat) : Nat :=
  Nat.find (exists_prime_family k)

example : primeFamilySize 13 [1] = 6 := by
  native_decide

example : primeFamilySize 56003 [1, 2] = 7 := by
  native_decide

end ProjectEulerStatements.P51
