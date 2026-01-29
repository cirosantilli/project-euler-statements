import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P77

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

def primesUpTo (n : Nat) : List Nat :=
  (List.range (n + 1)).filter isPrime

def countPrimeSums (n : Nat) : Nat :=
  let ps := primesUpTo n
  let rec go (n : Nat) (ps : List Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        if n = 0 then 1
        else match ps with
          | [] => 0
          | p :: tl =>
              let withP := if p ≤ n then go (n - p) (p :: tl) fuel else 0
              let withoutP := go n tl fuel
              withP + withoutP
  go n ps (n + ps.length + 1)

def firstOver (limit target : Nat) : Nat :=
  match (List.find? (fun n => countPrimeSums n > target) (List.range (limit + 1))) with
  | some n => n
  | none => 0

def naive (limit target : Nat) : Nat :=
  firstOver limit target

example : countPrimeSums 10 = 5 := by
  native_decide

end ProjectEulerStatements.P77
