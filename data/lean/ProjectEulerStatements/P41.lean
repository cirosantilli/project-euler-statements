import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Sort

namespace ProjectEulerStatements.P41

def digitsBE (n : Nat) : List Nat :=
  (Nat.digits 10 n).reverse

def allDigitsOneToN (n : Nat) (l : List Nat) : Bool :=
  l.length = n &&
    l.eraseDups.length = n &&
    l.foldl (fun acc d => acc && decide (1 ≤ d ∧ d ≤ n)) true

def isPandigitalN (n x : Nat) : Bool :=
  allDigitsOneToN n (digitsBE x)

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

def largestPandigitalPrime (n : Nat) : Nat :=
  let digits := (List.range n).map (fun i => i + 1)
  let perms := digits.permutations
  let nums := perms.map (fun p => Nat.ofDigits 10 p.reverse)
  let candidates := nums.filter isPrime
  match candidates.mergeSort (fun a b => decide (a ≤ b)) with
  | [] => 0
  | l => (l[l.length - 1]?).getD 0

def naive (n : Nat) : Nat :=
  largestPandigitalPrime n

example : isPandigitalN 4 2143 = true := by
  native_decide

example : isPrime 2143 = true := by
  native_decide

end ProjectEulerStatements.P41
