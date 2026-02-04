import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P47

def distinctPrimeFactors (n : Nat) : Nat :=
  let factors :=
    (List.range (n + 1)).filter (fun p => p ≥ 2 ∧ n % p = 0 ∧ Nat.Prime p)
  factors.length

def hasNFactors (k m : Nat) : Bool :=
  decide (distinctPrimeFactors m = k)

/-- Brute-force search for the first number in a run of `n` consecutive integers
each with exactly `n` distinct prime factors. -/
def naive (n : Nat) : Nat :=
  let limit := 10 ^ (n + 3)
  let candidates := (List.range (limit + 1)).map (fun m => m + 2)
  match candidates.find? (fun i => (List.range n).all (fun j => hasNFactors n (i + j))) with
  | some i => i
  | none => 0

example : distinctPrimeFactors 14 = 2 := by
  native_decide

example : distinctPrimeFactors 15 = 2 := by
  native_decide

example : distinctPrimeFactors 644 = 3 := by
  native_decide

end ProjectEulerStatements.P47
