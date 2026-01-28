import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax

namespace ProjectEulerStatements.P26

def stripFactor (p n fuel : Nat) : Nat :=
  match fuel with
  | 0 => n
  | fuel + 1 =>
      if n % p = 0 then
        stripFactor p (n / p) fuel
      else
        n

def reducedDenom (n : Nat) : Nat :=
  let n1 := stripFactor 2 n n
  stripFactor 5 n1 n1

def cycleLenAux (d : Nat) (fuel : Nat) : Nat :=
  let rec go (r k fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        if r = 1 then
          k
        else
          go ((r * 10) % d) (k + 1) fuel
  if d = 0 then 0 else go (10 % d) 1 fuel

def cycleLen (d : Nat) : Nat :=
  let d' := reducedDenom d
  if d' = 1 then 0 else cycleLenAux d' d'

noncomputable def naive (limit : Nat) : Nat :=
  match (List.argmax (fun d => cycleLen d) (List.range limit)) with
  | some d => d
  | none => 0

example : cycleLen 7 = 6 := by
  native_decide

example : cycleLen 6 = 1 := by
  native_decide

end ProjectEulerStatements.P26
