import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Tactic

namespace ProjectEulerStatements.P26

def stripFactor (p n : Nat) : Nat :=
  if hpn : p ≤ 1 then
    (by
      have _ := hpn
      exact n)
  else if hn : n = 0 then
    (by
      have _ := hn
      exact 0)
  else if n % p = 0 then
    stripFactor p (n / p)
  else
    n
termination_by n
decreasing_by
  have hp : 1 < p := Nat.lt_of_not_ge hpn
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  exact Nat.div_lt_self hn' hp

def reducedDenom (n : Nat) : Nat :=
  let n1 := stripFactor 2 n
  stripFactor 5 n1

def cycleLenAux (d : Nat) : Nat :=
  let rec go (r k steps : Nat) : Nat :=
    match steps with
    | 0 => 0
    | steps + 1 =>
        if r = 1 then
          k
        else
          go ((r * 10) % d) (k + 1) steps
  if d = 0 then 0 else go (10 % d) 1 d

def cycleLen (d : Nat) : Nat :=
  let d' := reducedDenom d
  if d' = 1 then 0 else cycleLenAux d'

noncomputable def naive (limit : Nat) : Nat :=
  match (List.argmax (fun d => cycleLen d) (List.range limit)) with
  | some d => d
  | none => 0

example : cycleLen 7 = 6 := by
  native_decide

example : cycleLen 6 = 1 := by
  native_decide

end ProjectEulerStatements.P26
