import ProjectEulerStatements.Lib.TotientMaximum

/-! Strict cross-multiplication updates retain the least maximizer in an increasing scan. -/
namespace ProjectEulerStatements.TotientMaximum
set_option Elab.async false

def better (a b : Nat) : Bool :=
  if a.totient = 0 ∨ b.totient = 0 then false
  else decide (b * a.totient < a * b.totient)

def visit (best candidate : Nat) : Nat := if better candidate best then candidate else best

def bestUpTo : Nat → Nat
  | 0 => 1
  | n + 1 => visit (bestUpTo n) (n + 1)

def referenceResult (limit : Int) : Nat := bestUpTo limit.toNat

theorem visit_zero (best : Nat) : visit best 0 = best := by
  simp only [visit, better, Nat.totient_zero, true_or, if_true, Bool.false_eq_true, if_false]

theorem visit_positive (best candidate : Nat) (bestPositive : 0 < best)
    (candidatePositive : 0 < candidate) :
    visit best candidate = if ratio best < ratio candidate then candidate else best := by
  have bestPhi := (Nat.totient_pos.mpr bestPositive).ne'
  have candidatePhi := (Nat.totient_pos.mpr candidatePositive).ne'
  simp only [visit, better, bestPhi, candidatePhi, or_self, if_false, decide_eq_true_eq,
    ratio_lt_iff best candidate bestPositive candidatePositive]

theorem bestUpTo_zero : bestUpTo 0 = 1 := rfl

theorem bestUpTo_one : bestUpTo 1 = 1 := by
  change visit 1 1 = 1
  rw [visit_positive 1 1 (by decide) (by decide), if_neg (lt_irrefl _)]

theorem maximum_step (limit best : Nat) (maximum : LeastMaximum limit best) :
    LeastMaximum (limit + 1) (visit best (limit + 1)) := by
  rw [visit_positive best (limit + 1) maximum.positive (by omega)]
  by_cases improved : ratio best < ratio (limit + 1)
  · rw [if_pos improved]
    refine ⟨by omega, le_rfl, ?_, ?_⟩
    · intro n positive bounded
      by_cases last : n = limit + 1
      · subst n; exact le_rfl
      · exact (maximum.dominates n positive (by omega)).trans improved.le
    · intro n positive bounded same
      by_cases last : n = limit + 1
      · subst n; exact le_rfl
      · have previous := maximum.dominates n positive (by omega)
        rw [same] at previous
        exact False.elim ((not_lt_of_ge previous) improved)
  · rw [if_neg improved]
    refine ⟨maximum.positive, maximum.bounded.trans (Nat.le_succ _), ?_, ?_⟩
    · intro n positive bounded
      by_cases last : n = limit + 1
      · subst n; exact le_of_not_gt improved
      · exact maximum.dominates n positive (by omega)
    · intro n positive bounded same
      by_cases last : n = limit + 1
      · subst n; exact maximum.bounded.trans (Nat.le_succ _)
      · exact maximum.least n positive (by omega) same

theorem bestUpTo_maximum (limit : Nat) (positive : 0 < limit) :
    LeastMaximum limit (bestUpTo limit) := by
  induction limit with
  | zero => omega
  | succ limit ih =>
      by_cases initial : limit = 0
      · subst limit
        rw [bestUpTo_one]
        refine ⟨by decide, le_rfl, ?_, ?_⟩
        · intro n positive bounded
          have same : n = 1 := by omega
          subst n
          exact le_rfl
        · intro n positive bounded _
          omega
      · exact maximum_step limit (bestUpTo limit) (ih (by omega))

theorem fold_range_best (limit : Nat) :
    (List.range (limit + 1)).foldl visit 1 = bestUpTo limit := by
  induction limit with
  | zero => exact visit_zero 1
  | succ limit ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, ih, bestUpTo]

theorem maximum_unique (limit a b : Nat) (left : LeastMaximum limit a)
    (right : LeastMaximum limit b) : a = b := by
  have same : ratio a = ratio b :=
    le_antisymm (right.dominates a left.positive left.bounded)
      (left.dominates b right.positive right.bounded)
  exact le_antisymm (left.least b right.positive right.bounded same.symm)
    (right.least a left.positive left.bounded same)

end ProjectEulerStatements.TotientMaximum
