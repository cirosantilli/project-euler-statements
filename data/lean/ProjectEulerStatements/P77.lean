import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace ProjectEulerStatements.P77

def isPrime (n : Nat) : Bool :=
  decide (Nat.Prime n)

def primesUpTo (n : Nat) : List Nat :=
  (List.range (n + 1)).filter isPrime

def countPrimeSums (n : Nat) : Nat :=
  let ps := primesUpTo n
  let rec go (n : Nat) (ps : List Nat) : Nat :=
    if hn : n = 0 then
      (by
        have _ := hn
        exact 1)
    else match ps with
      | [] => 0
      | p :: tl =>
          if h0 : p = 0 then
            (by
              have _ := h0
              exact go n tl)
          else
            let withP := if hp : p ≤ n then
              (by
                have _ := hp
                exact go (n - p) (p :: tl))
            else 0
            let withoutP := go n tl
            withP + withoutP
  termination_by n + ps.length
  decreasing_by
    all_goals
      simp
      try omega
  go n ps

def firstOver (limit target : Nat) : Nat :=
  match (List.find? (fun n => countPrimeSums n > target) (List.range (limit + 1))) with
  | some n => n
  | none => 0

def naive (limit target : Nat) : Nat :=
  firstOver limit target

example : countPrimeSums 10 = 5 := by
  native_decide

end ProjectEulerStatements.P77
