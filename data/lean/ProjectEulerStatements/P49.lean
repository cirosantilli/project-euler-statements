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

def seqFrom (a d len : Nat) : List Nat :=
  (List.range len).map (fun i => a + i * d)

def allPrime (l : List Nat) : Bool :=
  l.all isPrime

def allPerm (l : List Nat) : Bool :=
  match l with
  | [] => true
  | x :: xs => xs.all (fun y => isPermutation x y)

/-- Brute-force search for `seqlen`-long arithmetic sequences of `n`-digit primes
whose members are pairwise digit permutations. -/
def naive (n seqlen : Nat) : List (List Nat) :=
  if _ : n = 0 ∨ seqlen < 2 then
    []
  else
    let lower := 10 ^ (n - 1)
    let upper := 10 ^ n
    (List.range upper).foldr (fun a acc =>
      (List.range upper).foldr (fun d acc2 =>
        let last := a + (seqlen - 1) * d
        let s := seqFrom a d seqlen
        if decide (lower ≤ a ∧ d > 0 ∧ last < upper) &&
            allPrime s && allPerm s then
          s :: acc2
        else acc2) acc) []

def concatSeq (t : Nat × Nat × Nat) : Nat :=
  let a := t.1
  let b := t.2.1
  let c := t.2.2
  let lb := (Nat.digits 10 b).length
  let lc := (Nat.digits 10 c).length
  a * 10 ^ lb * 10 ^ lc + b * 10 ^ lc + c

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
