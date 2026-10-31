import ProjectEulerStatements.Lib.DigitFactorialChains

/-! Positive starting values whose digit-factorial orbit has the requested size. -/
namespace ProjectEulerStatements.P74
set_option Elab.async false

abbrev nextTerm := DigitFactorialChains.nextTerm
abbrev chainLen := DigitFactorialChains.chainLen

def countChains (limit target : Nat) : Nat :=
  ((List.range' 1 (limit - 1)).filter (fun n => decide (chainLen n = target))).length

/-- Signed source calls count the same positive starts, including empty and impossible requests. -/
def result (limit target : Int) : Int :=
  ((List.range' 1 (limit - 1).toNat).filter
    (fun n => decide ((chainLen n : Int) = target))).length

/-- Count positive starts below the signed bound whose distinct-term chain
has the desired length. -/
def naive (limit target : Int) : Int := result limit target

theorem result_nat (limit target : Nat) :
    result limit target = (countChains limit target : Int) := by
  have same : ((limit : Int) - 1).toNat = limit - 1 := by omega
  simp [result, countChains, same]

theorem result_empty (limit target : Int) (empty : limit ≤ 1) : result limit target = 0 := by
  have size : (limit - 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
  simp [result, size]

theorem result_nonpositive (limit target : Int) (impossible : target ≤ 0) :
    result limit target = 0 := by
  unfold result
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · intro start _
    have positive : 0 < (chainLen start : Int) :=
      Int.natCast_pos.mpr (DigitFactorialChains.chainLen_positive start)
    simpa only [decide_eq_true_eq] using ne_of_gt (lt_of_le_of_lt impossible positive)

theorem countChains_zero (target : Nat) : countChains 0 target = 0 := rfl

theorem countChains_one (target : Nat) : countChains 1 target = 0 := rfl

theorem countChains_target_zero (limit : Nat) : countChains limit 0 = 0 := by
  unfold countChains
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · intro start _
    simpa only [decide_eq_true_eq] using
      (Nat.ne_of_gt (DigitFactorialChains.chainLen_positive start))

end ProjectEulerStatements.P74
