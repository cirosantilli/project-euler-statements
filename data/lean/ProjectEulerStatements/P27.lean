import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Prime.Basic

namespace ProjectEulerStatements.P27

def quad (a b : Int) (n : Nat) : Int :=
  let z : Int := n
  z * z + a * z + b

def isPrimeInt (z : Int) : Bool :=
  (decide (z > 1)) && decide (Nat.Prime z.toNat)

def consecPrimeLen (a b : Int) (fuel : Nat) : Nat :=
  let rec go (n fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        if isPrimeInt (quad a b n) then
          1 + go (n + 1) fuel
        else
          0
  go 0 fuel

noncomputable def naive (limitA limitB fuel : Nat) : Int :=
  let as := (List.range (2 * limitA + 1)).map (fun i => (i : Int) - limitA)
  let bs := (List.range (2 * limitB + 1)).map (fun i => (i : Int) - limitB)
  let pairs :=
    as.foldr (fun a acc => (bs.map (fun b => (a, b))) ++ acc) []
  let best :=
    match List.argmax (fun p => consecPrimeLen p.1 p.2 fuel) pairs with
    | some p => p
    | none => (0, 0)
  best.1 * best.2

example : consecPrimeLen 1 41 100 = 40 := by
  native_decide

example : consecPrimeLen (-79) 1601 100 = 80 := by
  native_decide

example : (-79 : Int) * 1601 = -126479 := by
  native_decide

end ProjectEulerStatements.P27
