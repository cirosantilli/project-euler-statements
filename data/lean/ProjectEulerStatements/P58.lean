import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P58

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

/-- Number of diagonal primes for side length `2k+1`. -/
def diagPrimeCount : Nat → Nat
  | 0 => 0
  | k + 1 =>
      let side := 2 * (k + 1) + 1
      let sq := side ^ 2
      let step := side - 1
      let corners := [sq, sq - step, sq - 2 * step, sq - 3 * step]
      diagPrimeCount k + (corners.filter isPrime).length

/-- Total numbers on diagonals for side length `2k+1`. -/
def diagTotal (k : Nat) : Nat :=
  let side := 2 * k + 1
  2 * side - 1

/-- Whether prime ratio on diagonals is below `num/den` for side length `2k+1`. -/
def ratioBelow (k num den : Nat) : Bool :=
  let p := diagPrimeCount k
  let t := diagTotal k
  den * p < num * t

/-- Existence of a layer where the ratio falls below `num/den`. -/
theorem exists_ratio_below (num den : Nat) : ∃ k, ratioBelow k num den = true := by
  sorry

/-- Side length of the square spiral where the prime ratio first falls below `num/den`. -/
def naive (num den : Nat) : Nat :=
  let k := Nat.find (exists_ratio_below num den)
  2 * k + 1

example : diagPrimeCount 3 = 8 := by
  native_decide

example : diagTotal 3 = 13 := by
  native_decide

end ProjectEulerStatements.P58
