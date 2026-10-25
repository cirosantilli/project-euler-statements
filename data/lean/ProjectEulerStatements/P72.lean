import ProjectEulerStatements.Lib.ReducedFractionCount

set_option linter.style.header false

/-! Exhaustive counting of reduced fractions below each denominator of a signed bound. -/
namespace ProjectEulerStatements.P72

abbrev countReduced := ReducedFractionCount.countReduced

def totalCount (limit : Int) : Nat :=
  ((List.range (limit + 1).toNat).map (fun d => if 1 < d then countReduced d else 0)).sum

def naive (limit : Int) : Nat := totalCount limit

theorem naive_eq_result (limit : Int) : naive limit = ReducedFractionCount.result limit := by
  unfold naive totalCount ReducedFractionCount.result
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  simp only [ReducedFractionCount.contribution, countReduced,
    ReducedFractionCount.countReduced_eq_totient]

end ProjectEulerStatements.P72
