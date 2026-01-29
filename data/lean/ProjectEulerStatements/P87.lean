import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P87

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

def primesBelow (limit : Nat) : List Nat :=
  (List.range limit).filter isPrime

def countSums (limit : Nat) : Nat :=
  let ps := primesBelow (Nat.sqrt limit + 1)
  let sums :=
    ps.foldr (fun p acc =>
      ps.foldr (fun q acc2 =>
        ps.foldr (fun r acc3 =>
          let s := p^2 + q^3 + r^4
          if s < limit then s :: acc3 else acc3) acc2) acc) []
  sums.eraseDups.length

def naive (limit : Nat) : Nat :=
  countSums limit

example : countSums 50 = 4 := by
  native_decide

end ProjectEulerStatements.P87
