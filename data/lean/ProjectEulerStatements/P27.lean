import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace ProjectEulerStatements.P27

def quad (a b : Int) (n : Nat) : Int :=
  let z : Int := n
  z * z + a * z + b

def isPrimeInt (z : Int) : Bool :=
  (decide (z > 1)) && decide (Nat.Prime z.toNat)

lemma quad_add (a b : Int) (n p : Nat) :
    quad a b (n + p) =
      quad a b n + (p : Int) * (2 * (n : Int) + (p : Int) + a) := by
  dsimp [quad]
  ring

lemma quad_add_of_eq (a b : Int) (n p : Nat) (hp : quad a b n = (p : Int)) :
    quad a b (n + p) = (p : Int) * (1 + 2 * (n : Int) + (p : Int) + a) := by
  calc
    quad a b (n + p)
        = quad a b n + (p : Int) * (2 * (n : Int) + (p : Int) + a) := quad_add a b n p
    _ = (p : Int) * (1 + 2 * (n : Int) + (p : Int) + a) := by
          simp [hp]
          ring

lemma quad_add_dvd (a b : Int) (n p : Nat) (hp : quad a b n = (p : Int)) :
    (p : Int) ∣ quad a b (n + p) := by
  refine ⟨1 + 2 * (n : Int) + (p : Int) + a, ?_⟩
  simp [quad_add_of_eq a b n p hp]

def consecPrimeBound (b : Int) : Nat :=
  Int.natAbs b + 1

lemma quad_bound_dvd (a b : Int) :
    (Int.ofNat (Int.natAbs b)) ∣ quad a b (consecPrimeBound b - 1) := by
  set p : Nat := Int.natAbs b
  have hnp : consecPrimeBound b - 1 = p := by
    simp [consecPrimeBound, p]
  rw [hnp]
  obtain hb | hb := Int.natAbs_eq b
  · have hb' : b = (p : Int) := by simpa [p] using hb
    have hp : quad a b 0 = (p : Int) := by
      simp [quad, hb']
    have hdiv := quad_add_dvd a b 0 p hp
    have hdiv' : (p : Int) ∣ quad a b p := by
      simpa [Nat.zero_add] using hdiv
    exact hdiv'
  · refine ⟨(p : Int) + a - 1, ?_⟩
    have hb' : b = -(p : Int) := by simpa [p] using hb
    calc
      quad a b p = (p : Int) * (p : Int) + a * (p : Int) + b := by
        dsimp [quad]
      _ = (p : Int) * (p : Int) + a * (p : Int) + -(p : Int) := by
        rw [hb']
      _ = (p : Int) * ((p : Int) + a - 1) := by
        ring

def consecPrimeLen (a b : Int) : Nat :=
  let bound := consecPrimeBound b
  let rec go (n fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 =>
        if isPrimeInt (quad a b n) then
          1 + go (n + 1) fuel
        else
          0
  go 0 bound

/-- Project a * b where `a` and `b` are the Naturals below `limitA` and `limitB`
    such that $n^2 + an + b$ has the longest sequence of consecutive primest starting for n=0. -/
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
