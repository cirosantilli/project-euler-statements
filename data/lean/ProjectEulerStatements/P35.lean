import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ProjectEulerStatements.P35

def digitsBE (n : Nat) : List Nat :=
  (Nat.digits 10 n).reverse
def digitsToNat (l : List Nat) : Nat :=
  Nat.ofDigits 10 l.reverse

def rotations (l : List Nat) : List (List Nat) :=
  let len := l.length
  (List.range len).map (fun i => l.drop i ++ l.take i)

def listAll (l : List Bool) : Bool :=
  l.foldl (fun acc b => acc && b) true

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

def isCircularPrime (n : Nat) : Bool :=
  if n < 2 then
    false
  else
    let rots := rotations (digitsBE n)
    listAll (rots.map (fun r => isPrime (digitsToNat r)))

def countCircularPrimes (limit : Nat) : Nat :=
  ((Finset.range limit).filter (fun n => isCircularPrime n)).card

def naive (limit : Nat) : Nat :=
  countCircularPrimes limit

example : isCircularPrime 197 = true := by
  native_decide

example : countCircularPrimes 100 = 13 := by
  native_decide

end ProjectEulerStatements.P35
