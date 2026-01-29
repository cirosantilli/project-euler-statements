import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Sort

namespace ProjectEulerStatements.P49

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

def digitsSorted (n : Nat) : List Nat :=
  (Nat.digits 10 n).mergeSort (fun a b => decide (a ≤ b))

def isPermutation (a b : Nat) : Bool :=
  digitsSorted a = digitsSorted b

def findSeq (limit : Nat) : List (Nat × Nat × Nat) :=
  (List.range limit).foldr (fun a acc =>
    (List.range limit).foldr (fun b acc2 =>
      let c := b + (b - a)
      if decide (a < b ∧ c < limit) && isPrime a && isPrime b && isPrime c &&
          isPermutation a b && isPermutation b c then
        (a, b, c) :: acc2
      else acc2) acc) []

def concatSeq (t : Nat × Nat × Nat) : Nat :=
  let a := t.1
  let b := t.2.1
  let c := t.2.2
  let lb := (Nat.digits 10 b).length
  let lc := (Nat.digits 10 c).length
  a * 10 ^ lb * 10 ^ lc + b * 10 ^ lc + c

def naive (limit : Nat) : List (Nat × Nat × Nat) :=
  findSeq limit

example : isPrime 1487 = true := by
  native_decide

example : isPrime 4817 = true := by
  native_decide

example : isPrime 8147 = true := by
  native_decide

example : isPermutation 1487 4817 = true := by
  native_decide

example : isPermutation 4817 8147 = true := by
  native_decide

end ProjectEulerStatements.P49
