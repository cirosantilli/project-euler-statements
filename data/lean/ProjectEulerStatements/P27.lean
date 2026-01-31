import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Divisibility.Basic

namespace ProjectEulerStatements.P27

def quad (a b : Int) (n : Nat) : Int :=
  let z : Int := n
  z * z + a * z + b

def isPrimeInt (z : Int) : Bool :=
  (decide (z > 1)) && decide (Nat.Prime z.toNat)

def consecPrimeBound (a b : Int) : Nat :=
  Int.natAbs b * (Int.natAbs a + 2)

lemma quad_bound_dvd (a b : Int) :
    (Int.ofNat (Int.natAbs b)) ∣ quad a b (consecPrimeBound a b) := by
  set b' : Nat := Int.natAbs b
  set k : Nat := Int.natAbs a + 2
  have hb : (b' : Int) ∣ b := by
    refine (Int.natCast_dvd (n := b) (m := b')).2 ?_
    simp [b']
  have hz : (b' : Int) ∣ (b' * k : Nat) := by
    refine (Int.dvd_natCast (m := (b' : Int)) (n := b' * k)).2 ?_
    simp [b']
  have hz2 : (b' : Int) ∣ ((b' * k : Nat) : Int) * ((b' * k : Nat) : Int) := by
    exact (dvd_mul_of_dvd_left (α := Int) hz _)
  have haz : (b' : Int) ∣ a * ((b' * k : Nat) : Int) := by
    have : (b' : Int) ∣ ((b' * k : Nat) : Int) * a := by
      exact (dvd_mul_of_dvd_left (α := Int) hz _)
    simpa [mul_comm] using this
  dsimp [consecPrimeBound, quad, b', k]
  exact dvd_add (α := Int) (dvd_add (α := Int) hz2 haz) hb

def consecPrimeLen (a b : Int) : Nat :=
  let bound := consecPrimeBound a b
  let rec go (n fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        if isPrimeInt (quad a b n) then
          1 + go (n + 1) fuel
        else
          0
  go 0 bound

def naive (limitA limitB : Nat) : Int :=
  let as := (List.range (2 * limitA + 1)).map (fun i => (i : Int) - limitA)
  let bs := (List.range (2 * limitB + 1)).map (fun i => (i : Int) - limitB)
  let pairs :=
    as.foldr (fun a acc => (bs.map (fun b => (a, b))) ++ acc) []
  let best :=
    match List.argmax (fun p => consecPrimeLen p.1 p.2) pairs with
    | some p => p
    | none => (0, 0)
  best.1 * best.2

example : consecPrimeLen 1 41 = 40 := by
  native_decide

example : consecPrimeLen (-79) 1601 = 80 := by
  native_decide

example : (-79 : Int) * 1601 = -126479 := by
  native_decide

end ProjectEulerStatements.P27
