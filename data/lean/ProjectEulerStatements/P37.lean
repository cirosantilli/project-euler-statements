import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ProjectEulerStatements.P37

def digitsBE (n : Nat) : List Nat :=
  (Nat.digits 10 n).reverse
def digitsToNat (l : List Nat) : Nat :=
  Nat.ofDigits 10 l.reverse

def listAll (l : List Bool) : Bool :=
  l.foldl (fun acc b => acc && b) true

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

def truncations (n : Nat) : List Nat :=
  let ds := digitsBE n
  let len := ds.length
  let lefts := (List.range (len - 1)).map (fun i => digitsToNat (ds.drop (i + 1)))
  let rights := (List.range (len - 1)).map (fun i => digitsToNat (ds.take (len - i - 1)))
  lefts ++ rights

def isTruncatablePrime (n : Nat) : Bool :=
  if n ≤ 7 then
    false
  else
    isPrime n && listAll ((truncations n).map isPrime)

def sumTruncatable (limit : Nat) : Nat :=
  ((Finset.range limit).filter (fun n => isTruncatablePrime n)).sum (fun n => n)

def naive (limit : Nat) : Nat :=
  sumTruncatable limit

example : isTruncatablePrime 3797 = true := by
  native_decide

end ProjectEulerStatements.P37
