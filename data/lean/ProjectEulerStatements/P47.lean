import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P47

def distinctPrimeFactors (n : Nat) : Nat :=
  let factors :=
    (List.range (n + 1)).filter (fun p => p ≥ 2 ∧ n % p = 0 ∧ Nat.Prime p)
  factors.length

def hasNFactors (k n : Nat) : Bool :=
  decide (distinctPrimeFactors n = k)

def firstRun (k run limit : Nat) : Nat :=
  let rec go (i fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        if (List.range run).all (fun j => hasNFactors k (i + j)) then
          i
        else
          go (i + 1) fuel
  go 2 limit

def naive (k run limit : Nat) : Nat :=
  firstRun k run limit

example : distinctPrimeFactors 14 = 2 := by
  native_decide

example : distinctPrimeFactors 15 = 2 := by
  native_decide

example : distinctPrimeFactors 644 = 3 := by
  native_decide

end ProjectEulerStatements.P47
