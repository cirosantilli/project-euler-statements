import Mathlib.NumberTheory.Divisors
import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-! The bounded divisor enumeration used by the Python reference functions. -/
namespace ProjectEulerStatements.DivisorEnumeration

/-- Enumerate positive divisors in increasing order; zero has an empty list. -/
def values (n : Nat) : List Nat :=
  (List.range' 1 n).filter fun d => decide (n % d = 0)

/-- The not-yet-tested candidates of a bounded divisor scan. -/
def remaining (n position : Nat) : List Nat :=
  (List.range' position (n + 1 - position)).filter fun d => decide (n % d = 0)

theorem remaining_done (n position : Nat) (finished : n + 1 ≤ position) :
    remaining n position = [] := by
  simp [remaining, Nat.sub_eq_zero_of_le finished]

theorem remaining_step (n position : Nat) (active : position < n + 1) :
    remaining n position = if n % position = 0 then
      position :: remaining n (position + 1) else remaining n (position + 1) := by
  have count : n + 1 - position = n + 1 - (position + 1) + 1 := by omega
  rw [remaining, count, List.range'_succ, List.filter_cons]
  simp only [decide_eq_true_eq]
  rfl

theorem remaining_one (n : Nat) : remaining n 1 = values n := by
  simp [remaining, values]

theorem nodup (n : Nat) : (values n).Nodup :=
  (List.nodup_range' (s := 1) (n := n)).filter _

theorem toFinset_eq_divisors (n : Nat) : (values n).toFinset = n.divisors := by
  ext d
  simp only [List.mem_toFinset, values, List.mem_filter, List.mem_range', decide_eq_true_eq,
    Nat.mem_divisors]
  constructor
  · rintro ⟨⟨i, bound, equal⟩, divides⟩
    exact ⟨Nat.dvd_of_mod_eq_zero divides, by omega⟩
  · rintro ⟨divides, nonzero⟩
    have positive := Nat.pos_of_dvd_of_pos divides (Nat.pos_of_ne_zero nonzero)
    have bound := Nat.le_of_dvd (Nat.pos_of_ne_zero nonzero) divides
    exact ⟨⟨d - 1, by omega, by omega⟩, Nat.mod_eq_zero_of_dvd divides⟩

theorem length_eq_card_divisors (n : Nat) : (values n).length = n.divisors.card := by
  rw [← toFinset_eq_divisors]
  exact (List.toFinset_card_of_nodup (nodup n)).symm

end ProjectEulerStatements.DivisorEnumeration
