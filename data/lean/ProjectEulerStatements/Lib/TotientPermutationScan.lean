import ProjectEulerStatements.Lib.TotientPermutationMinimum

/-! Moving decimal intervals and cached-totient updates in the optimized ratio scan. -/
namespace ProjectEulerStatements.TotientPermutation
set_option Elab.async false

/-- Before the boundary test, the cursor can be exactly at the upper endpoint. -/
def WidthBefore (n width : Nat) : Prop := 10 ^ width ≤ n ∧ n ≤ 10 ^ (width + 1)

def advanceWidth (n width : Nat) : Nat :=
  if n = 10 ^ (width + 1) then width + 1 else width

/-- The boundary assignment selects the unique active decimal interval. -/
theorem advanceWidth_active (n width : Nat) (before : WidthBefore n width) :
    10 ^ advanceWidth n width ≤ n ∧ n < 10 ^ (advanceWidth n width + 1) := by
  by_cases boundary : n = 10 ^ (width + 1)
  · rw [advanceWidth, if_pos boundary]
    refine ⟨boundary.ge, ?_⟩
    rw [boundary, pow_succ]
    have positive : 0 < 10 ^ (width + 1) := pow_pos (by decide) _
    omega
  · rw [advanceWidth, if_neg boundary]
    exact ⟨before.1, by have upper := before.2; omega⟩

theorem advanceWidth_next (n width : Nat) (before : WidthBefore n width) :
    WidthBefore (n + 1) (advanceWidth n width) := by
  obtain ⟨lower, upper⟩ := advanceWidth_active n width before
  exact ⟨by omega, by omega⟩

/-- Multiplying the old upper endpoint by ten gives the new upper endpoint. -/
theorem advanceWidth_values (n width : Nat) :
    (if n = 10 ^ (width + 1) then (10 ^ (width + 1), 10 ^ (width + 1) * 10)
      else (10 ^ width, 10 ^ (width + 1))) =
      (10 ^ advanceWidth n width, 10 ^ (advanceWidth n width + 1)) := by
  by_cases boundary : n = 10 ^ (width + 1)
  · simp only [advanceWidth, if_pos boundary]
    simp only [pow_succ]
  · simp only [advanceWidth, if_neg boundary]

def screen (n width : Nat) : Bool :=
  decide (10 ^ width ≤ n.totient ∧ n.totient < 10 ^ (width + 1)) &&
    decide (((n : Int) - n.totient) % 9 = 0) && isPermutation n n.totient

/-- The source's inexpensive filters reject no decimal totient permutation. -/
theorem screen_eq (n width : Nat) (lower : 10 ^ width ≤ n)
    (upper : n < 10 ^ (width + 1)) : screen n width = isPermutation n n.totient := by
  cases same : isPermutation n n.totient with
  | false => simp [screen, same]
  | true =>
      obtain ⟨phiLower, phiUpper, residue⟩ := filters n width same lower upper
      simp [screen, same, phiLower, phiUpper, residue]

/-- The cached totient is relevant only when a nonzero incumbent exists. -/
def PhiMatches (best bestPhi : Nat) : Prop := best ≠ 0 → bestPhi = best.totient

theorem improvement_matches (n best bestPhi : Nat) (large : 2 ≤ n)
    (matched : PhiMatches best bestPhi) :
    decide (best = 0 ∨ n * bestPhi < best * n.totient) =
      decide (best = 0 ∨ better n best = true) := by
  by_cases zero : best = 0
  · simp only [zero, true_or, decide_true]
  · have phiN := (Nat.totient_pos.mpr (by omega : 0 < n)).ne'
    have phiBest := (Nat.totient_pos.mpr (by omega : 0 < best)).ne'
    simp only [zero, false_or, matched zero, better, phiN, phiBest, or_self, if_false,
      decide_eq_true_eq]

/-- One optimized scan step, including all three screens and the cached ratio comparison. -/
def scanStep (n width best bestPhi : Nat) : Nat × Nat :=
  if screen n width then
    if best = 0 ∨ n * bestPhi < best * n.totient then (n, n.totient) else (best, bestPhi)
  else (best, bestPhi)

/-- The optimized step chooses exactly the reference's strict record update. -/
theorem scanStep_first (n width best bestPhi : Nat) (large : 2 ≤ n)
    (lower : 10 ^ width ≤ n) (upper : n < 10 ^ (width + 1))
    (matched : PhiMatches best bestPhi) : (scanStep n width best bestPhi).1 = visit best n := by
  have eligibleN : eligible n ↔ isPermutation n n.totient = true := by
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have choice := improvement_matches n best bestPhi large matched
  have compared : (best = 0 ∨ n * bestPhi < best * n.totient) ↔
      best = 0 ∨ better n best = true := by
    simpa only [decide_eq_true_eq] using Bool.eq_iff_iff.mp choice
  simp only [scanStep, screen_eq n width lower upper, visit, eligibleN]
  by_cases accepted : isPermutation n n.totient = true
  · simp only [accepted, if_true, compared]
    split <;> rfl
  · simp only [accepted]
    rfl

/-- Updating both incumbent fields maintains the cached-totient invariant. -/
theorem scanStep_matches (n width best bestPhi : Nat) (matched : PhiMatches best bestPhi) :
    PhiMatches (scanStep n width best bestPhi).1 (scanStep n width best bestPhi).2 := by
  simp only [scanStep]
  split
  · split
    · exact fun _ => rfl
    · exact matched
  · exact matched

theorem visit_one (best : Nat) : visit best 1 = best := by
  have absent : ¬ eligible 1 := by rintro ⟨large, _⟩; omega
  simp only [visit, if_neg absent]

/-- Starting at two omits only the two candidates which can never be eligible. -/
theorem fold_from_two (limit : Nat) (positive : 1 ≤ limit) :
    (List.range' 2 (limit - 1)).foldl visit 0 = result (limit : Int) := by
  have count : 2 + (limit - 1) = limit + 1 := by omega
  have split : List.range (limit + 1) = [0, 1] ++ List.range' 2 (limit - 1) := by
    have joined := List.range'_append_1 (s := 0) (m := 2) (n := limit - 1)
    simpa only [count, Nat.zero_add, ← List.range_eq_range'] using joined.symm
  rw [result, Int.toNat_natCast, ← fold_range_best, split, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, visit_zero, visit_one]

/-- Every bound below two has no eligible positive candidate. -/
theorem result_small (limit : Int) (small : limit < 2) : result limit = 0 := by
  have bounded : limit.toNat ≤ 1 := by omega
  have spec := bestUpTo_spec limit.toNat
  by_contra nonzero
  have chosen := spec.selected nonzero
  have large := chosen.1.1
  omega

end ProjectEulerStatements.TotientPermutation
