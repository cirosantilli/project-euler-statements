import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Finite searches for the reduced proper fraction immediately below a rational target. -/
namespace ProjectEulerStatements.FractionSearch
set_option Elab.async false

abbrev Pair := Nat × Nat

def ratio (p : Pair) : ℚ := (p.1 : ℚ) / p.2

def Valid (a b : Nat) (p : Pair) : Prop :=
  0 < p.2 ∧ p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ p.1 * b < a * p.2

instance (a b : Nat) (p : Pair) : Decidable (Valid a b p) := inferInstanceAs
  (Decidable (0 < p.2 ∧ p.1 < p.2 ∧ Nat.Coprime p.1 p.2 ∧ p.1 * b < a * p.2))

def Selected (limit : Nat) (p : Pair) : Prop := p = (0, 1) ∨ p.2 ≤ limit

structure Best (a b limit : Nat) (p : Pair) : Prop where
  valid : Valid a b p
  selected : Selected limit p
  dominates : ∀ q, Valid a b q → q.2 ≤ limit → ratio q ≤ ratio p

theorem zero_valid (a b : Nat) (positive : 0 < a) : Valid a b (0, 1) := by
  simp [Valid, positive]

theorem ratio_le_iff (p q : Pair) (hp : 0 < p.2) (hq : 0 < q.2) :
    ratio p ≤ ratio q ↔ p.1 * q.2 ≤ q.1 * p.2 := by
  rw [ratio, ratio, div_le_div_iff₀ (by exact_mod_cast hp) (by exact_mod_cast hq)]
  exact_mod_cast Iff.rfl

theorem ratio_lt_iff (p q : Pair) (hp : 0 < p.2) (hq : 0 < q.2) :
    ratio p < ratio q ↔ p.1 * q.2 < q.1 * p.2 := by
  rw [ratio, ratio, div_lt_div_iff₀ (by exact_mod_cast hp) (by exact_mod_cast hq)]
  exact_mod_cast Iff.rfl

theorem ratio_eq_iff (p q : Pair) (hp : 0 < p.2) (hq : 0 < q.2) :
    ratio p = ratio q ↔ p.1 * q.2 = q.1 * p.2 := by
  rw [ratio, ratio, div_eq_div_iff (by exact_mod_cast hp.ne') (by exact_mod_cast hq.ne')]
  exact_mod_cast Iff.rfl

theorem reduced_unique (p q : Pair) (hp : 0 < p.2) (hq : 0 < q.2)
    (cp : Nat.Coprime p.1 p.2) (cq : Nat.Coprime q.1 q.2)
    (same : ratio p = ratio q) : p = q := by
  have cross := (ratio_eq_iff p q hp hq).mp same
  have pdvd : p.2 ∣ q.2 := cp.symm.dvd_of_dvd_mul_left (by rw [cross]; exact dvd_mul_left _ _)
  have qdvd : q.2 ∣ p.2 := cq.symm.dvd_of_dvd_mul_left (by rw [← cross]; exact dvd_mul_left _ _)
  have denominators := Nat.dvd_antisymm pdvd qdvd
  have numerators : p.1 = q.1 := by
    rw [denominators] at cross
    exact Nat.eq_of_mul_eq_mul_right hq cross
  exact Prod.ext numerators denominators

theorem Best.unique {a b limit : Nat} {p q : Pair}
    (hp : Best a b limit p) (hq : Best a b limit q) : p = q := by
  have upper (s t : Pair) (hs : Best a b limit s) (ht : Best a b limit t) :
      ratio s ≤ ratio t := by
    rcases hs.selected with zero | bounded
    · rw [zero, ratio]
      simp only [Nat.cast_zero, Nat.cast_one, zero_div]
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact ht.dominates s hs.valid bounded
  exact reduced_unique p q hp.valid.1 hq.valid.1 hp.valid.2.2.1 hq.valid.2.2.1
    (le_antisymm (upper p q hp hq) (upper q p hq hp))

def choose (best candidate : Pair) : Pair :=
  if candidate.1 * best.2 > best.1 * candidate.2 then candidate else best

theorem choose_mem (best candidate : Pair) :
    choose best candidate = best ∨ choose best candidate = candidate := by
  unfold choose
  split <;> simp

theorem choose_ratio (best candidate : Pair) (hb : 0 < best.2) (hc : 0 < candidate.2) :
    ratio (choose best candidate) = max (ratio best) (ratio candidate) := by
  by_cases improved : best.1 * candidate.2 < candidate.1 * best.2
  · rw [choose, if_pos improved, max_eq_right
      ((ratio_lt_iff best candidate hb hc).mpr improved).le]
  · rw [choose, if_neg improved, max_eq_left
      ((ratio_le_iff candidate best hc hb).mpr (by omega))]

def visit (a b : Nat) (best candidate : Pair) : Pair :=
  if Valid a b candidate then choose best candidate else best

theorem visit_valid {a b : Nat} {best candidate : Pair} (hb : Valid a b best) :
    Valid a b (visit a b best candidate) := by
  by_cases hc : Valid a b candidate
  · rw [visit, if_pos hc]
    rcases choose_mem best candidate with h | h
    · rwa [h]
    · rwa [h]
  · rwa [visit, if_neg hc]

theorem visit_selected {a b limit : Nat} {best candidate : Pair}
    (hb : Selected limit best) (hc : candidate.2 ≤ limit) :
    Selected limit (visit a b best candidate) := by
  unfold visit
  split
  · rcases choose_mem best candidate with h | h
    · rwa [h]
    · rw [h]
      exact Or.inr hc
  · exact hb

theorem visit_increases {a b : Nat} {best candidate : Pair} (hb : Valid a b best) :
    ratio best ≤ ratio (visit a b best candidate) := by
  by_cases hc : Valid a b candidate
  · rw [visit, if_pos hc, choose_ratio best candidate hb.1 hc.1]
    exact le_max_left _ _
  · rw [visit, if_neg hc]

theorem visit_dominates {a b : Nat} {best candidate : Pair}
    (hb : Valid a b best) (hc : Valid a b candidate) :
    ratio candidate ≤ ratio (visit a b best candidate) := by
  rw [visit, if_pos hc, choose_ratio best candidate hb.1 hc.1]
  exact le_max_right _ _

/-- Every visited valid fraction is bounded by the final result, in any traversal order. -/
theorem fold_spec (a b limit : Nat) (candidates : List Pair) (best : Pair)
    (valid : Valid a b best) (selected : Selected limit best)
    (bounded : ∀ c ∈ candidates, c.2 ≤ limit) :
    Valid a b (candidates.foldl (visit a b) best) ∧
    Selected limit (candidates.foldl (visit a b) best) ∧
    ratio best ≤ ratio (candidates.foldl (visit a b) best) ∧
    ∀ c ∈ candidates, Valid a b c → ratio c ≤ ratio (candidates.foldl (visit a b) best) := by
  induction candidates generalizing best with
  | nil => simp [valid, selected]
  | cons head tail ih =>
      have headBound := bounded head (by simp)
      obtain ⟨v, s, inc, dom⟩ := ih (visit a b best head) (visit_valid valid)
        (visit_selected selected headBound) (fun c hc => bounded c (by simp [hc]))
      refine ⟨v, s, (visit_increases valid).trans inc, ?_⟩
      intro c member hc
      rcases List.mem_cons.mp member with same | rest
      · subst c
        exact (visit_dominates valid hc).trans inc
      · exact dom c rest hc

def row (a b d : Nat) (best : Pair) : Pair :=
  (List.range d).foldl (fun p n => visit a b p (n, d)) best

def exhaustive (a b : Nat) : Nat → Pair → Pair
  | 0, best => best
  | d + 1, best => exhaustive a b d (row a b (d + 1) best)

theorem row_spec (a b limit d : Nat) (best : Pair) (valid : Valid a b best)
    (selected : Selected limit best) (bounded : d ≤ limit) :
    Valid a b (row a b d best) ∧ Selected limit (row a b d best) ∧
    ratio best ≤ ratio (row a b d best) ∧
    ∀ n, n < d → Valid a b (n, d) → ratio (n, d) ≤ ratio (row a b d best) := by
  have mapped := fold_spec a b limit ((List.range d).map (fun n => (n, d))) best valid selected
    (by intro c hc; obtain ⟨n, _, rfl⟩ := List.mem_map.mp hc; exact bounded)
  simp only [List.foldl_map] at mapped
  exact ⟨mapped.1, mapped.2.1, mapped.2.2.1,
    fun n hn hc => mapped.2.2.2 (n, d) (List.mem_map.mpr ⟨n, List.mem_range.mpr hn, rfl⟩) hc⟩

theorem exhaustive_spec (a b limit count : Nat) (best : Pair) (valid : Valid a b best)
    (selected : Selected limit best) (bounded : count ≤ limit) :
    Valid a b (exhaustive a b count best) ∧ Selected limit (exhaustive a b count best) ∧
    ratio best ≤ ratio (exhaustive a b count best) ∧
    ∀ q, Valid a b q → q.2 ≤ count → ratio q ≤ ratio (exhaustive a b count best) := by
  induction count generalizing best with
  | zero =>
      refine ⟨valid, selected, le_rfl, ?_⟩
      intro q hq small
      have := hq.1
      omega
  | succ count ih =>
      obtain ⟨rv, rs, ri, rd⟩ := row_spec a b limit (count + 1) best valid selected bounded
      obtain ⟨ev, es, ei, ed⟩ := ih (row a b (count + 1) best) rv rs (by omega)
      refine ⟨ev, es, ri.trans ei, ?_⟩
      intro q hq hbound
      by_cases last : q.2 = count + 1
      · have qr := rd q.1 (last ▸ hq.2.1) (last ▸ hq)
        have qr' : ratio q ≤ ratio (row a b (count + 1) best) := by
          simpa only [← last, Prod.mk.eta] using qr
        exact qr'.trans ei
      · exact ed q hq (by omega)

theorem exhaustive_best (a b limit : Nat) (positive : 0 < a) :
    Best a b limit (exhaustive a b limit (0, 1)) := by
  obtain ⟨v, s, _, d⟩ := exhaustive_spec a b limit limit (0, 1)
    (zero_valid a b positive) (Or.inl rfl) le_rfl
  exact ⟨v, s, d⟩

/-- The largest numerator strictly below the target at the given denominator. -/
def ceiling (a b d : Nat) : Nat := (a * d - 1) / b

theorem ceiling_below (a b d : Nat) (ha : 0 < a) (hab : a < b) (hd : 0 < d) :
    ceiling a b d < d ∧ ceiling a b d * b < a * d := by
  have product := Nat.mul_pos ha hd
  have cut : a * d - 1 < a * d := by omega
  have bound := Nat.mul_le_mul_right d hab.le
  constructor
  · exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by
      simpa only [Nat.mul_comm] using cut.trans_le bound)
  · have mulBound := Nat.div_mul_le_self (a * d - 1) b
    exact mulBound.trans_lt cut

theorem ceiling_largest (a b d n : Nat) (hb : 0 < b) (below : n * b < a * d) :
    n ≤ ceiling a b d :=
  (Nat.le_div_iff_mul_le hb).mpr (by omega)

/-- Reducing a candidate preserves its value and strictly lowers its denominator. -/
theorem reduce_ceiling (a b d : Nat) (ha : 0 < a) (hab : a < b) (hd : 0 < d)
    (unreduced : ¬ Nat.Coprime (ceiling a b d) d) :
    ∃ q : Pair, Valid a b q ∧ q.2 < d ∧ ratio q = ratio (ceiling a b d, d) := by
  let m := ceiling a b d
  let g := Nat.gcd m d
  have gp : 0 < g := Nat.gcd_pos_of_pos_right m hd
  have large : 1 < g := by
    have different : g ≠ 1 := unreduced
    omega
  have nm : m / g * g = m := Nat.div_mul_cancel (Nat.gcd_dvd_left m d)
  have nd : d / g * g = d := Nat.div_mul_cancel (Nat.gcd_dvd_right m d)
  have qp : 0 < d / g := Nat.div_gcd_pos_of_pos_right m hd
  have lower : d / g < d := Nat.div_lt_self hd large
  obtain ⟨proper, below⟩ := ceiling_below a b d ha hab hd
  have reducedProper : m / g < d / g := by nlinarith
  have reducedBelow : m / g * b < a * (d / g) := by nlinarith
  refine ⟨(m / g, d / g), ⟨qp, reducedProper,
    Nat.coprime_div_gcd_div_gcd gp, reducedBelow⟩, lower, ?_⟩
  apply (ratio_eq_iff _ _ qp hd).mpr
  change m / g * d = m * (d / g)
  calc
    m / g * d = m / g * (d / g * g) := by rw [nd]
    _ = (m / g * g) * (d / g) := by ac_rfl
    _ = m * (d / g) := by rw [nm]

def optimizedStep (a b d : Nat) (best : Pair) : Pair :=
  let n := ceiling a b d
  if n = 0 then best
  else if Nat.Coprime n d then choose best (n, d) else best

def optimizedUpTo (a b : Nat) : Nat → Pair
  | 0 => (0, 1)
  | d + 1 => optimizedStep a b (d + 1) (optimizedUpTo a b d)

/-- A finite ascending fold is the recursive optimized search at its final denominator. -/
theorem optimized_fold (a b first count : Nat) :
    (List.range' (first + 1) count).foldl (fun p d => optimizedStep a b d p)
      (optimizedUpTo a b first) = optimizedUpTo a b (first + count) := by
  induction count generalizing first with
  | zero => simp
  | succ count ih =>
      rw [List.range'_succ, List.foldl_cons]
      change (List.range' (first + 1 + 1) count).foldl (fun p d => optimizedStep a b d p)
        (optimizedUpTo a b (first + 1)) = _
      simpa only [Nat.add_assoc, Nat.add_comm 1 count] using ih (first + 1)

theorem optimized_step_best (a b limit : Nat) (ha : 0 < a) (hab : a < b)
    (best : Pair) (previous : Best a b limit best) :
    Best a b (limit + 1) (optimizedStep a b (limit + 1) best) := by
  let d := limit + 1
  let n := ceiling a b d
  have hd : 0 < d := by omega
  obtain ⟨proper, below⟩ := ceiling_below a b d ha hab hd
  have selected : Selected d best := previous.selected.imp id (by omega)
  have finish (next : Pair) (v : Valid a b next) (s : Selected d next)
      (increases : ratio best ≤ ratio next) (ceilingBound : ratio (n, d) ≤ ratio next) :
      Best a b d next := by
    refine ⟨v, s, ?_⟩
    intro q hq bounded
    by_cases last : q.2 = d
    · have numeratorBound := ceiling_largest a b d q.1 (by omega) (last ▸ hq.2.2.2)
      have ratioBound : ratio q ≤ ratio (n, d) :=
        (ratio_le_iff q (n, d) hq.1 hd).mpr (by
          change q.1 * d ≤ n * q.2
          rw [last]
          exact Nat.mul_le_mul_right d numeratorBound)
      exact ratioBound.trans ceilingBound
    · exact (previous.dominates q hq (by omega)).trans increases
  by_cases zero : n = 0
  · have nonnegative : 0 ≤ ratio best := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have unchanged : optimizedStep a b d best = best := by
      simp only [optimizedStep, show ceiling a b d = n from rfl, if_pos zero]
    rw [unchanged]
    exact finish best previous.valid selected le_rfl (by simpa [ratio, zero] using nonnegative)
  · by_cases coprime : Nat.Coprime n d
    · have valid : Valid a b (n, d) := ⟨hd, proper, coprime, below⟩
      have changed : optimizedStep a b d best = choose best (n, d) := by
        simp only [optimizedStep, show ceiling a b d = n from rfl, if_neg zero, if_pos coprime]
      rw [changed]
      have v : Valid a b (choose best (n, d)) := by
        rcases choose_mem best (n, d) with same | same
        · rw [same]; exact previous.valid
        · rw [same]; exact valid
      have s : Selected d (choose best (n, d)) := by
        rcases choose_mem best (n, d) with same | same
        · rwa [same]
        · rw [same]; exact Or.inr le_rfl
      exact finish (choose best (n, d)) v s
        (by rw [choose_ratio best (n, d) previous.valid.1 hd]; exact le_max_left _ _)
        (by rw [choose_ratio best (n, d) previous.valid.1 hd]; exact le_max_right _ _)
    · obtain ⟨q, hq, smaller, same⟩ := reduce_ceiling a b d ha hab hd coprime
      have bound := previous.dominates q hq (by omega)
      have unchanged : optimizedStep a b d best = best := by
        simp only [optimizedStep, show ceiling a b d = n from rfl, if_neg zero, if_neg coprime]
      rw [unchanged]
      exact finish best previous.valid selected le_rfl (by rwa [← same])

theorem optimized_best (a b limit : Nat) (positive : 0 < a) (proper : a < b) :
    Best a b limit (optimizedUpTo a b limit) := by
  induction limit with
  | zero =>
      refine ⟨zero_valid a b positive, Or.inl rfl, ?_⟩
      intro q hq bound
      have := hq.1
      omega
  | succ limit ih => exact optimized_step_best a b limit positive proper _ ih

theorem optimized_eq_exhaustive (a b limit : Nat) (positive : 0 < a) (proper : a < b) :
    optimizedUpTo a b limit = exhaustive a b limit (0, 1) :=
  (optimized_best a b limit positive proper).unique (exhaustive_best a b limit positive)

end ProjectEulerStatements.FractionSearch
