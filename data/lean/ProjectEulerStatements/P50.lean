import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.MinMax

namespace ProjectEulerStatements.P50

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

def primesBelow (limit : Nat) : List Nat :=
  (List.range limit).filter isPrime

def prefixSums (l : List Nat) : List Nat :=
  l.foldl (fun acc x => acc ++ [x + (acc[acc.length - 1]? ).getD 0]) []

def sumRange (pref : List Nat) (i j : Nat) : Nat :=
  if i = 0 then (pref[j - 1]?).getD 0 else
    (pref[j - 1]?).getD 0 - (pref[i - 1]?).getD 0

def longestPrimeSum (limit : Nat) : Nat :=
  let ps := primesBelow limit
  let pref := prefixSums ps
  let n := ps.length
  let candidates :=
    (List.range (n + 1)).foldr (fun i acc =>
      (List.range (n + 1)).foldr (fun j acc2 =>
        if i < j then
          let s := sumRange pref i j
          if s < limit && isPrime s then
            (j - i, s) :: acc2
          else acc2
        else acc2) acc) []
  match List.argmax (fun p => p.1) candidates with
  | some p => p.2
  | none => 0

def naive (limit : Nat) : Nat :=
  longestPrimeSum limit

example : 41 = 2 + 3 + 5 + 7 + 11 + 13 := by
  native_decide

example : (sumRange (prefixSums (primesBelow 100)) 0 6) = 41 := by
  native_decide

example : (sumRange (prefixSums (primesBelow 1000)) 3 24) = 953 := by
  native_decide

end ProjectEulerStatements.P50
