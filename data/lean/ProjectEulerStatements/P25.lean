import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace ProjectEulerStatements.P25

abbrev fib := Nat.fib

def numDigits (n : Nat) : Nat :=
  (Nat.digits 10 n).length

lemma numDigits_mono : Monotone numDigits := by
  intro a b hab
  simpa [numDigits] using (Nat.le_digits_len_le (b := 10) (n := a) (m := b) hab)

lemma fib_mono : Monotone fib := by
  simpa [fib] using (Nat.fib_mono)

lemma numDigits_fib_mono : Monotone (fun n => numDigits (fib n)) :=
  numDigits_mono.comp fib_mono

lemma numDigits_ge_of_pow_le {digits n : Nat} (hpos : 0 < digits)
    (h : 10 ^ (digits - 1) ≤ n) : digits ≤ numDigits n := by
  have hlen : digits - 1 < numDigits n := by
    exact (Nat.lt_digits_length_iff (b := 10) (k := digits - 1) (n := n) (by decide)).2 h
  have h1 : 1 ≤ digits := Nat.succ_le_iff.mp hpos
  have hlen' : digits - 1 + 1 ≤ numDigits n := by
    exact (Nat.succ_le_iff).2 hlen
  simpa [Nat.sub_add_cancel h1, Nat.succ_eq_add_one] using hlen'

lemma exists_fib_digits (digits : Nat) : ∃ n, digits ≤ numDigits (fib n) := by
  by_cases h0 : digits = 0
  · refine ⟨0, ?_⟩
    simp [h0, numDigits]
  · have hpos : 0 < digits := Nat.pos_of_ne_zero h0
    let N : Nat := 10 ^ (digits - 1)
    let n : Nat := max 5 N
    have hN : N ≤ n := le_max_right _ _
    have hn5 : 5 ≤ n := le_max_left _ _
    have hfib : n ≤ fib n := by
      simpa [fib] using (Nat.le_fib_self (n := n) hn5)
    have hNfib : N ≤ fib n := le_trans hN hfib
    refine ⟨n, ?_⟩
    have hpow : 10 ^ (digits - 1) ≤ fib n := by
      simpa [N] using hNfib
    exact numDigits_ge_of_pow_le (n := fib n) hpos hpow

def fibBound (digits : Nat) : Nat :=
  max 5 (10 ^ (digits - 1))

lemma fibBound_spec (digits : Nat) : digits ≤ numDigits (fib (fibBound digits)) := by
  by_cases h0 : digits = 0
  · simp [fibBound, h0, numDigits]
  · have hpos : 0 < digits := Nat.pos_of_ne_zero h0
    have hN : 10 ^ (digits - 1) ≤ fibBound digits := le_max_right _ _
    have hn5 : 5 ≤ fibBound digits := le_max_left _ _
    have hfib : fibBound digits ≤ fib (fibBound digits) := by
      simpa [fib] using (Nat.le_fib_self (n := fibBound digits) hn5)
    have hpow : 10 ^ (digits - 1) ≤ fib (fibBound digits) := le_trans hN hfib
    exact numDigits_ge_of_pow_le (n := fib (fibBound digits)) hpos hpow

def firstFibWithDigits.go (digits : Nat) (i : Nat) : Nat → Nat
  | 0 => i
  | k + 1 =>
      if digits ≤ numDigits (fib i) then
        i
      else
        firstFibWithDigits.go digits (i + 1) k

def firstFibWithDigits (digits : Nat) : Nat :=
  let bound := fibBound digits
  firstFibWithDigits.go digits 0 (bound + 1)

/-- Index of the first Fibonacci number to contain `n` digits. -/
def naive (n : Nat) : Nat :=
  firstFibWithDigits n

example : fib 12 = 144 := by
  native_decide

example : naive 3 = 12 := by
  native_decide

end ProjectEulerStatements.P25
