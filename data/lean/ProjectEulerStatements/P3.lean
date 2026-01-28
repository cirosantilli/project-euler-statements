import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P3

def primeFactorSet (n : Nat) : Finset Nat :=
  (Finset.range (n + 1)).filter (fun k => 2 ≤ k ∧ k ∣ n ∧ Nat.Prime k)

def naive2 (n : Nat) : Nat :=
  if h : (primeFactorSet n).Nonempty then
    (primeFactorSet n).max' h
  else
    0

def naive (n : Nat) : Nat :=
  let rec go : Nat -> Nat
    | 0 => 0
    | k + 1 =>
        let k1 := k + 1
        if 2 ≤ k1 ∧ k1 ∣ n ∧ Nat.Prime k1 then k1 else go k
  go n

theorem naive_eq_naive2 (n : Nat) : naive n = naive2 n := by
  -- TODO: show the recursive scan returns the maximum element of `primeFactorSet`.
  -- A proof should proceed by induction on `n` (or the recursion variable in `go`).
  sorry

example : naive 13195 = 29 := by
  native_decide

end ProjectEulerStatements.P3
