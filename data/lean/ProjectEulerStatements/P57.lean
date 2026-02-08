import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P57

/-- One step for sqrt(2) continued fraction convergents. -/
def nextFrac (p q : Nat) : Nat × Nat :=
  (p + 2 * q, p + q)

/-- The `n`-th expansion (0-based) of the sqrt(2) continued fraction. -/
def convergent : Nat → Nat × Nat
  | 0 => (3, 2)
  | n + 1 =>
      let t := convergent n
      nextFrac t.1 t.2

/-- Count how many of the first `k` expansions have more digits in numerator. -/
def naive (k : Nat) : Nat :=
  (List.range k).foldl (fun acc i =>
    let t := convergent i
    let ln := (Nat.digits 10 t.1).length
    let ld := (Nat.digits 10 t.2).length
    if ln > ld then acc + 1 else acc) 0

example :
    let t := convergent 7
    (Nat.digits 10 t.1).length > (Nat.digits 10 t.2).length = true := by
  native_decide

end ProjectEulerStatements.P57
