import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Range
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Exhaustive right-truncatable-prime frontiers in an arbitrary numeral base.
The tree has no prescribed depth or number of successful values. -/
namespace ProjectEulerStatements.TruncatablePrimeBase

set_option Elab.async false

def RightPrime (base n : Nat) : Prop :=
  ∀ count, 0 < n / base ^ count → Nat.Prime (n / base ^ count)

def LeftPrime (base n : Nat) : Prop :=
  ∀ count, 0 < count → base ^ count ≤ n → Nat.Prime (n % base ^ count)

def Truncatable (base n : Nat) : Prop :=
  base ≤ n ∧ RightPrime base n ∧ LeftPrime base n

def roots (base : Nat) : List Nat :=
  (List.range base).filter fun n => decide (Nat.Prime n)

def children (base n : Nat) : List Nat :=
  ((List.range' 1 (base - 1)).map (fun digit => base * n + digit)).filter
    fun candidate => decide (Nat.Prime candidate)

def level (base : Nat) : Nat → List Nat
  | 0 => roots base
  | depth + 1 => (level base depth).flatMap (children base)

theorem mem_roots (base n : Nat) : n ∈ roots base ↔ n < base ∧ Nat.Prime n := by
  simp [roots]

theorem mem_children (base parent n : Nat) (valid : 2 ≤ base) :
    n ∈ children base parent ↔
      ∃ digit, 0 < digit ∧ digit < base ∧ n = base * parent + digit ∧ Nat.Prime n := by
  simp only [children, List.mem_filter, List.mem_map, decide_eq_true_eq,
    List.mem_range'_1]
  constructor
  · rintro ⟨⟨digit, ⟨lower, upper⟩, rfl⟩, prime⟩
    exact ⟨digit, lower, by omega, rfl, prime⟩
  · rintro ⟨digit, lower, upper, rfl, prime⟩
    exact ⟨⟨digit, ⟨lower, by omega⟩, rfl⟩, prime⟩

theorem right_prime (base n : Nat) (positive : 0 < n) (right : RightPrime base n) :
    Nat.Prime n := by
  simpa using right 0 (by simpa using positive)

theorem right_parent (base n : Nat) (right : RightPrime base n) : RightPrime base (n / base) := by
  intro count positive
  have equal : n / base / base ^ count = n / base ^ (count + 1) := by
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm base]
  rw [equal] at positive ⊢
  exact right (count + 1) positive

theorem right_of_parent (base n : Nat) (prime : Nat.Prime n)
    (parent : RightPrime base (n / base)) : RightPrime base n := by
  intro count positive
  cases count with
  | zero => simpa using prime
  | succ count =>
      have equal : n / base / base ^ count = n / base ^ (count + 1) := by
        rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm base]
      exact equal ▸ parent count (equal.symm ▸ positive)

theorem small_right (base n : Nat) (valid : 2 ≤ base) (small : n < base)
    (prime : Nat.Prime n) : RightPrime base n := by
  intro count positive
  cases count with
  | zero => simpa using prime
  | succ count =>
      have power : base ≤ base ^ (count + 1) :=
        by simpa only [Nat.pow_one] using
          Nat.pow_le_pow_right (by omega : 0 < base) (show 1 ≤ count + 1 by omega)
      rw [Nat.div_eq_of_lt (small.trans_le power)] at positive
      omega

theorem right_last_digit (base n : Nat) (valid : 2 ≤ base) (large : base ≤ n)
    (right : RightPrime base n) : 0 < n % base := by
  have positive : 0 < n / base := Nat.div_pos large (by omega)
  have parentPrime := right_prime base (n / base) positive (right_parent base n right)
  have prime := right_prime base n (by omega) right
  have strict : base < n := by
    have division := Nat.div_add_mod n base
    have product := Nat.mul_le_mul_left base parentPrime.two_le
    omega
  by_contra zero
  have divides : base ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
  rcases (Nat.dvd_prime prime).mp divides with one | self
  · omega
  · omega

/-- Each level contains exactly all right-truncatable primes of that digit width. -/
theorem mem_level (base depth n : Nat) (valid : 2 ≤ base) :
    n ∈ level base depth ↔
      base ^ depth ≤ n ∧ n < base ^ (depth + 1) ∧ RightPrime base n := by
  induction depth generalizing n with
  | zero =>
      rw [level, mem_roots]
      simp only [Nat.pow_zero, Nat.zero_add, Nat.pow_one]
      constructor
      · rintro ⟨small, prime⟩
        exact ⟨by have := prime.two_le; omega, small, small_right base n valid small prime⟩
      · rintro ⟨positive, small, right⟩
        exact ⟨small, right_prime base n (by omega) right⟩
  | succ depth ih =>
      rw [level, List.mem_flatMap]
      constructor
      · rintro ⟨parent, member, child⟩
        obtain ⟨lower, upper, right⟩ := (ih parent).mp member
        obtain ⟨digit, digitPositive, digitSmall, rfl, prime⟩ :=
          (mem_children base parent n valid).mp child
        have parentEq : (base * parent + digit) / base = parent := by
          rw [Nat.mul_add_div (by omega : 0 < base), Nat.div_eq_of_lt digitSmall, Nat.add_zero]
        refine ⟨?_, ?_, right_of_parent base _ prime (parentEq.symm ▸ right)⟩
        · rw [Nat.pow_succ]
          nlinarith
        · rw [Nat.pow_succ]
          nlinarith
      · rintro ⟨lower, upper, right⟩
        have basePositive : 0 < base := by omega
        have powerPositive : 0 < base ^ depth := Nat.pow_pos basePositive
        have large : base ≤ n := by
          rw [Nat.pow_succ] at lower
          nlinarith
        have parentLower : base ^ depth ≤ n / base := by
          apply (Nat.le_div_iff_mul_le basePositive).mpr
          simpa only [Nat.pow_succ] using lower
        have parentUpper : n / base < base ^ (depth + 1) := by
          apply (Nat.div_lt_iff_lt_mul basePositive).mpr
          simpa only [Nat.pow_succ] using upper
        refine ⟨n / base, (ih _).mpr ⟨parentLower, parentUpper, right_parent base n right⟩, ?_⟩
        apply (mem_children base (n / base) n valid).mpr
        exact ⟨n % base, right_last_digit base n valid large right,
          Nat.mod_lt n basePositive, (Nat.div_add_mod n base).symm,
          right_prime base n (by omega) right⟩

/-- No positive right-truncatable prime lies outside the generated tree. -/
theorem right_mem_level (base n : Nat) (valid : 2 ≤ base) (positive : 0 < n)
    (right : RightPrime base n) : ∃ depth, n ∈ level base depth := by
  let width := (Nat.digits base n).length
  have nonempty : 0 < width := by
    simp only [width, List.length_pos_iff_ne_nil]
    exact Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  have lower : base ^ (width - 1) ≤ n := by
    apply (Nat.lt_digits_length_iff valid n).mp
    change width - 1 < width
    omega
  have upper : n < base ^ width :=
    (Nat.digits_length_le_iff valid n).mp (by rfl)
  exact ⟨width - 1, (mem_level base _ n valid).mpr
    ⟨lower, by simpa only [Nat.sub_add_cancel nonempty] using upper, right⟩⟩

theorem level_after_empty (base depth extra : Nat) (empty : level base depth = []) :
    level base (depth + extra) = [] := by
  induction extra with
  | zero => simpa using empty
  | succ extra ih => simp [level, ih]

def Exhausts (base : Nat) : Prop := ∃ depth, level base depth = []

/-- Exhaustion is equivalent to a finite digit-depth bound, rather than an imposed cap. -/
theorem exhausts_iff_bounded (base : Nat) (valid : 2 ≤ base) :
    Exhausts base ↔ ∃ bound, ∀ n, 0 < n → RightPrime base n → n < bound := by
  constructor
  · rintro ⟨depth, empty⟩
    refine ⟨base ^ depth, ?_⟩
    intro n positive right
    obtain ⟨foundDepth, member⟩ := right_mem_level base n valid positive right
    have before : foundDepth < depth := by
      by_contra beyond
      have equal : depth + (foundDepth - depth) = foundDepth := by omega
      have missing := level_after_empty base depth (foundDepth - depth) empty
      rw [equal] at missing
      simp [missing] at member
    have upper := ((mem_level base foundDepth n valid).mp member).2.1
    exact upper.trans_le (Nat.pow_le_pow_right (by omega : 0 < base) before)
  · rintro ⟨bound, bounded⟩
    refine ⟨bound, List.eq_nil_iff_forall_not_mem.mpr ?_⟩
    intro n member
    obtain ⟨lower, _, right⟩ := (mem_level base bound n valid).mp member
    have positive : 0 < n := lt_of_lt_of_le (Nat.pow_pos (by omega : 0 < base)) lower
    have growth : bound < base ^ bound := Nat.lt_pow_self valid
    have small := bounded n positive right
    omega

theorem children_ordered (base parent : Nat) : (children base parent).Pairwise (· < ·) := by
  apply List.Pairwise.filter
  apply List.pairwise_map.mpr
  exact (List.pairwise_lt_range' 1 (by decide)).imp (by intro a b smaller; omega)

theorem level_ordered (base depth : Nat) (valid : 2 ≤ base) :
    (level base depth).Pairwise (· < ·) := by
  induction depth with
  | zero => exact List.pairwise_lt_range.filter _
  | succ depth ih =>
      apply List.pairwise_flatMap.mpr
      refine ⟨fun parent _ => children_ordered base parent, ih.imp ?_⟩
      intro first second before x firstChild y secondChild
      obtain ⟨firstDigit, firstPositive, firstSmall, rfl, _⟩ :=
        (mem_children base first x valid).mp firstChild
      obtain ⟨secondDigit, secondPositive, secondSmall, rfl, _⟩ :=
        (mem_children base second y valid).mp secondChild
      nlinarith

/-- Candidates through a given number of expansion steps, excluding the roots. -/
def candidates (base depth : Nat) : List Nat :=
  (List.range depth).flatMap fun d => level base (d + 1)

theorem candidates_ordered (base depth : Nat) (valid : 2 ≤ base) :
    (candidates base depth).Pairwise (· < ·) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun d _ => level_ordered base (d + 1) valid, List.pairwise_lt_range.imp ?_⟩
  intro first second before x firstMember y secondMember
  have xUpper := ((mem_level base (first + 1) x valid).mp firstMember).2.1
  have yLower := ((mem_level base (second + 1) y valid).mp secondMember).1
  exact xUpper.trans_le ((Nat.pow_le_pow_right (by omega : 0 < base)
    (show first + 1 + 1 ≤ second + 1 by omega)).trans yLower)

/-- An empty frontier certifies that the accumulated list includes every candidate. -/
theorem mem_candidates_of_empty (base depth n : Nat) (valid : 2 ≤ base)
    (empty : level base depth = []) :
    n ∈ candidates base depth ↔ base ≤ n ∧ RightPrime base n := by
  constructor
  · intro member
    obtain ⟨d, _, member⟩ := List.mem_flatMap.mp member
    obtain ⟨lower, _, right⟩ := (mem_level base (d + 1) n valid).mp member
    have power : base ≤ base ^ (d + 1) := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right
        (by omega : 0 < base) (show 1 ≤ d + 1 by omega)
    exact ⟨power.trans lower, right⟩
  · rintro ⟨large, right⟩
    obtain ⟨foundDepth, member⟩ := right_mem_level base n valid (by omega) right
    have nonzero : foundDepth ≠ 0 := by
      intro zero
      subst foundDepth
      have small := ((mem_roots base n).mp member).1
      omega
    have before : foundDepth < depth := by
      by_contra beyond
      have equal : depth + (foundDepth - depth) = foundDepth := by omega
      have missing := level_after_empty base depth (foundDepth - depth) empty
      rw [equal] at missing
      simp [missing] at member
    apply List.mem_flatMap.mpr
    refine ⟨foundDepth - 1, List.mem_range.mpr (by omega), ?_⟩
    simpa only [Nat.sub_add_cancel (show 1 ≤ foundDepth by omega)] using member

def leftCheck (base n : Nat) : Bool :=
  (List.range' 1 ((Nat.digits base n).length - 1)).all
    fun count => decide (Nat.Prime (n % base ^ count))

theorem leftCheck_iff (base n : Nat) (valid : 2 ≤ base) :
    leftCheck base n = true ↔ LeftPrime base n := by
  simp only [leftCheck, List.all_eq_true, List.mem_range'_1, decide_eq_true_eq, LeftPrime]
  constructor
  · intro checks count positive power
    have within := (Nat.lt_digits_length_iff valid n).mpr power
    exact checks count ⟨positive, by omega⟩
  · intro checks count bounds
    have within : count < (Nat.digits base n).length := by omega
    exact checks count bounds.1 ((Nat.lt_digits_length_iff valid n).mp within)

def accepted (base depth : Nat) : List Nat :=
  (candidates base depth).filter (leftCheck base)

theorem accepted_nodup (base depth : Nat) (valid : 2 ≤ base) :
    (accepted base depth).Nodup :=
  ((candidates_ordered base depth valid).imp (by intro a b less; omega)).filter _

theorem mem_accepted_of_empty (base depth n : Nat) (valid : 2 ≤ base)
    (empty : level base depth = []) : n ∈ accepted base depth ↔ Truncatable base n := by
  simp only [accepted, List.mem_filter, mem_candidates_of_empty base depth n valid empty,
    leftCheck_iff base n valid, Truncatable, and_assoc]

/-- Different exhaustion witnesses describe the same sum of distinct primes. -/
theorem accepted_independent (base first second : Nat) (valid : 2 ≤ base)
    (firstEmpty : level base first = []) (secondEmpty : level base second = []) :
    accepted base first = accepted base second := by
  apply ((candidates_ordered base first valid).filter _).eq_of_mem_iff
    ((candidates_ordered base second valid).filter _)
  intro n
  change n ∈ accepted base first ↔ n ∈ accepted base second
  rw [mem_accepted_of_empty base first n valid firstEmpty,
    mem_accepted_of_empty base second n valid secondEmpty]

noncomputable def answer (base : Nat) (exhausts : Exhausts base) : Nat :=
  (accepted base (Nat.find exhausts)).sum

theorem answer_eq_sum (base depth : Nat) (valid : 2 ≤ base) (empty : level base depth = []) :
    answer base ⟨depth, empty⟩ = (accepted base depth).sum := by
  unfold answer
  rw [accepted_independent base _ depth valid
    (Nat.find_spec (show Exhausts base from ⟨depth, empty⟩)) empty]

end ProjectEulerStatements.TruncatablePrimeBase
