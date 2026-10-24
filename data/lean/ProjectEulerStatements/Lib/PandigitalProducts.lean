import ProjectEulerStatements.P32
import Lean.Elab.Tactic.Omega

/-! Total digit-mask computation used by the Python pandigital-product solver. -/
namespace ProjectEulerStatements.PandigitalProducts

/-- A negative mask reports a zero or repeated digit. -/
def digitMaskAux (n mask length : Nat) : Int × Nat :=
  if positive : 0 < n then
    let digit := n % 10
    if digit = 0 then (-1, 0)
    else
      let bit := 2 ^ (digit - 1)
      if mask &&& bit ≠ 0 then (-1, 0)
      else digitMaskAux (n / 10) (mask ||| bit) (length + 1)
  else (mask, length)
termination_by n
decreasing_by exact Nat.div_lt_self positive (by decide)

def digitMask (n : Nat) : Int × Nat := digitMaskAux n 0 0

@[simp] theorem digitMaskAux_zero (mask length : Nat) :
    digitMaskAux 0 mask length = ((mask : Int), length) := by
  rw [digitMaskAux]
  simp

theorem digitMaskAux_step (n mask length : Nat) (positive : 0 < n) :
    digitMaskAux n mask length =
      if n % 10 = 0 then (-1, 0)
      else if mask &&& 2 ^ (n % 10 - 1) ≠ 0 then (-1, 0)
      else digitMaskAux (n / 10) (mask ||| 2 ^ (n % 10 - 1)) (length + 1) := by
  rw [digitMaskAux]
  simp only [positive, ↓reduceDIte]

/-- The exact acceptance tests in the two optimized search loops. -/
def accepted (a b : Nat) : Bool :=
  let (ma, la) := digitMask a
  let (mb, lb) := digitMask b
  let (mp, lp) := digitMask (a * b)
  decide (0 ≤ ma ∧ 0 ≤ mb ∧ ma.toNat &&& mb.toNat = 0 ∧
    1000 ≤ a * b ∧ a * b ≤ 9999 ∧ 0 ≤ mp ∧
    (ma.toNat ||| mb.toNat) &&& mp.toNat = 0 ∧
    la + lb + lp = 9 ∧ (ma.toNat ||| mb.toNat ||| mp.toNat) = 511)

def lowerBound (lower a : Nat) : Nat := max lower ((1000 + a - 1) / a)
def upperBound (upper a : Nat) : Nat := min upper (9999 / a)

def row (lower upper a : Nat) : List Nat :=
  if (digitMask a).1 < 0 then []
  else ((List.range' (lowerBound lower a)
    (upperBound upper a + 1 - lowerBound lower a)).filter (accepted a)).map (a * ·)

def products : List Nat :=
  (List.range' 1 9).flatMap (row 1000 9999) ++ (List.range' 10 90).flatMap (row 100 999)

end ProjectEulerStatements.PandigitalProducts
