import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega

set_option linter.style.header false

/-! Complete numerator bounds for reduced proper fractions in an arbitrary rational interval. -/
namespace ProjectEulerStatements.FractionIntervalCount
set_option Elab.async false

structure Bounds where
  lowerNum : Int
  lowerDen : Int
  upperNum : Int
  upperDen : Int
  deriving DecidableEq

def Positive (p : Bounds) : Prop := 0 < p.lowerDen ∧ 0 < p.upperDen

def between (p : Bounds) (d n : Int) : Prop :=
  n * p.lowerDen > p.lowerNum * d ∧ n * p.upperDen < p.upperNum * d

instance (p : Bounds) (d n : Int) : Decidable (between p d n) := inferInstanceAs
  (Decidable (n * p.lowerDen > p.lowerNum * d ∧ n * p.upperDen < p.upperNum * d))

def accepted (p : Bounds) (d n : Int) : Prop := Int.gcd n d = 1 ∧ between p d n

instance (p : Bounds) (d n : Int) : Decidable (accepted p d n) := inferInstanceAs
  (Decidable (Int.gcd n d = 1 ∧ between p d n))

def count (predicate : Int → Prop) [DecidablePred predicate] (first stop : Int) : Nat :=
  ((Finset.Ico first stop).filter predicate).card

theorem count_empty (predicate : Int → Prop) [DecidablePred predicate] (first stop : Int)
    (finished : stop ≤ first) : count predicate first stop = 0 := by
  simp [count, Finset.Ico_eq_empty_of_le finished]

theorem count_step (predicate : Int → Prop) [DecidablePred predicate] (first stop : Int)
    (active : first < stop) :
    count predicate first stop =
      (if predicate first then 1 else 0) + count predicate (first + 1) stop := by
  have interval : Finset.Ico first stop = insert first (Finset.Ico (first + 1) stop) := by
    ext n
    simp only [Finset.mem_insert, Finset.mem_Ico]
    omega
  unfold count
  rw [interval]
  by_cases chosen : predicate first
  · simp [Finset.filter_insert, chosen, Finset.mem_filter, Finset.mem_Ico, Nat.add_comm]
  · simp [Finset.filter_insert, chosen]

def row (p : Bounds) (d : Int) : Nat := count (accepted p d) 1 d

def lower (p : Bounds) (d : Int) : Int := max 1 (p.lowerNum * d / p.lowerDen + 1)
def upper (p : Bounds) (d : Int) : Int := min (d - 1) ((p.upperNum * d - 1) / p.upperDen)

/-- The trimmed interval contains exactly the positive proper numerators between the endpoints. -/
theorem bounds_iff (p : Bounds) (positive : Positive p) (d n : Int) :
    lower p d ≤ n ∧ n ≤ upper p d ↔ 1 ≤ n ∧ n < d ∧ between p d n := by
  have lo : p.lowerNum * d / p.lowerDen + 1 ≤ n ↔ p.lowerNum * d < n * p.lowerDen := by
    have divided := Int.ediv_lt_iff_lt_mul (a := p.lowerNum * d) (b := n) positive.1
    omega
  have hi : n ≤ (p.upperNum * d - 1) / p.upperDen ↔ n * p.upperDen < p.upperNum * d := by
    rw [Int.le_ediv_iff_mul_le positive.2]
    omega
  simp only [lower, upper, max_le_iff, le_min_iff, lo, hi, between]
  omega

/-- Numerator pruning changes only the range, leaving the coprimality test unchanged. -/
theorem trimmed_eq_row (p : Bounds) (positive : Positive p) (d : Int) :
    count (fun n => Int.gcd n d = 1) (lower p d) (upper p d + 1) = row p d := by
  unfold count row
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ico, accepted]
  constructor
  · rintro ⟨⟨lo, hi⟩, coprime⟩
    obtain ⟨one, proper, inside⟩ := (bounds_iff p positive d n).mp ⟨lo, by omega⟩
    exact ⟨⟨one, proper⟩, coprime, inside⟩
  · rintro ⟨⟨one, proper⟩, coprime, inside⟩
    obtain ⟨lo, hi⟩ := (bounds_iff p positive d n).mpr ⟨one, proper, inside⟩
    exact ⟨⟨lo, by omega⟩, coprime⟩

def rows (p : Bounds) (first : Int) : Nat → Nat
  | 0 => 0
  | k + 1 => row p first + rows p (first + 1) k

def result (p : Bounds) (limit : Int) : Nat := rows p 2 (limit - 1).toNat

end ProjectEulerStatements.FractionIntervalCount
