import ProjectEulerStatements.Lib.PythagoreanPerimeterCountingProof

/-! Count all perimeters with exactly one unordered positive integer right triangle. -/
namespace ProjectEulerStatements.P75
set_option Elab.async false

def countSolutions (p : Nat) : Nat :=
  (List.range (p + 1)).foldl (fun acc a =>
    (List.range (p + 1)).foldl (fun acc2 b =>
      let c := p - a - b
      if a < b ∧ b < c ∧ a^2 + b^2 = c^2 then acc2 + 1 else acc2) acc) 0

def countSingular (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun acc p =>
    if countSolutions p = 1 then acc + 1 else acc) 0

theorem countSolutions_eq (p : Nat) : countSolutions p = P39.countSolutions p := rfl

def picked (first count : Nat) : Nat :=
  ((List.range' first count).filter (fun p => decide (countSolutions p = 1))).length

theorem count_fold (items : List Nat) (initial : Nat) :
    items.foldl (fun total p => if countSolutions p = 1 then total + 1 else total) initial =
      initial + (items.filter (fun p => decide (countSolutions p = 1))).length := by
  induction items generalizing initial with
  | nil => rfl
  | cons p rest ih =>
      by_cases chosen : countSolutions p = 1 <;> simp [chosen, ih, Nat.add_assoc, Nat.add_comm]

theorem countSingular_picked (limit : Nat) : countSingular limit = picked 0 (limit + 1) := by
  simpa only [countSingular, picked, Nat.zero_add, List.range_eq_range'] using
    count_fold (List.range (limit + 1)) 0

private theorem table_fold (limit : Nat) (items : List Nat)
    (bounded : ∀ p ∈ items, p ≤ limit) (initial : Nat) :
    items.foldl (fun total p => if PythagoreanPerimeterCounting.table limit p = 1
      then total + 1 else total) initial =
      items.foldl (fun total p => if countSolutions p = 1 then total + 1 else total) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons p rest ih =>
      have inside := bounded p (by simp)
      simp only [List.foldl_cons, PythagoreanPerimeterCounting.table_correct limit p inside,
        ← countSolutions_eq]
      apply ih
      intro n member
      exact bounded n (by simp [member])

theorem countSingular_table (limit : Nat) :
    (List.range (limit + 1)).foldl (fun total p =>
      if PythagoreanPerimeterCounting.table limit p = 1 then total + 1 else total) 0 =
        countSingular limit := by
  apply table_fold
  intro p member
  have inside := List.mem_range.mp member
  omega

def result (limit : Int) : Int := picked 0 (limit + 1).toNat

/-- Count singular perimeters below the inclusive signed bound; negative bounds give zero. -/
def naive (limit : Int) : Int := result limit

theorem result_nat (limit : Nat) : result limit = (countSingular limit : Int) := by
  have size : ((limit : Int) + 1).toNat = limit + 1 := by omega
  rw [result, size, ← countSingular_picked]

theorem result_negative (limit : Int) (negative : limit < 0) : result limit = 0 := by
  have empty : (limit + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
  simp [result, picked, empty]

end ProjectEulerStatements.P75
