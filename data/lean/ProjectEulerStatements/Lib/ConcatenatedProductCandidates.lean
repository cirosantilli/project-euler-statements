import ProjectEulerStatements.Lib.ConcatenatedProducts
import Mathlib.Data.List.Nodup

/-! The reference's candidate lists contain at most one entry per positive seed. -/
namespace ProjectEulerStatements.ConcatenatedProducts

open P38

def accepted (n k : Nat) : Bool :=
  decide (1 < k) && decide (numDigits (concatProduct n k) = 9) &&
    isPandigital1to9 (concatProduct n k)

def seedValues (n : Nat) : List Nat :=
  (List.range 9).filterMap fun i =>
    if accepted n (i + 1) then some (concatProduct n (i + 1)) else none

theorem accepted_nine (n k : Nat) (yes : accepted n k = true) :
    numDigits (concatProduct n k) = 9 := by
  simp only [accepted, Bool.and_eq_true, decide_eq_true_eq] at yes
  exact yes.1.2

theorem reference_inner (n : Nat) (items suffix : List Nat) :
    items.foldr (fun k acc =>
      if k + 1 ≤ 1 then acc
      else if numDigits (concatProduct n (k + 1)) = 9 &&
          isPandigital1to9 (concatProduct n (k + 1))
        then concatProduct n (k + 1) :: acc else acc) suffix =
      (items.filterMap fun k =>
        if accepted n (k + 1) then some (concatProduct n (k + 1)) else none) ++ suffix := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.foldr_cons, ih]
      by_cases zero : head = 0
      · subst head
        simp [accepted]
      · have positive : 0 < head := by omega
        by_cases nine : numDigits (concatProduct n (head + 1)) = 9
        · cases yes : isPandigital1to9 (concatProduct n (head + 1)) <;>
            simp [accepted, zero, positive, nine, yes]
        · simp [accepted, zero, positive, nine]

theorem naive_candidates (limit : Nat) :
    naive limit = listMax ((List.range (limit + 1)).flatMap seedValues) := by
  have inner (n : Nat) (suffix : List Nat) := reference_inner n (List.range 9) suffix
  simp only [naive, maxPandigital, inner]
  congr 1
  induction List.range (limit + 1) with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.foldr_cons, List.flatMap_cons, ih]
      rfl

theorem seedValues_zero : seedValues 0 = [] := by
  simp [seedValues, accepted, zero_product, numDigits]

private theorem select_unique (items : List Nat) (unique : items.Nodup) (target value : Nat) :
    (items.filterMap fun i => if i = target then some value else none) =
      if target ∈ items then [value] else [] := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      by_cases same : head = target
      · subst head
        simp [absent, ih tailUnique]
      · simp [same, Ne.symm same, ih tailUnique]

theorem seedValues_at_stop (n : Nat) (positive : 0 < n) :
    seedValues n = if accepted n (stopCount n) then [concatProduct n (stopCount n)] else [] := by
  have bounds := stopCount_bounds n positive
  by_cases yes : accepted n (stopCount n) = true
  · have replace (i : Nat) :
        (if accepted n (i + 1) then some (concatProduct n (i + 1)) else none) =
          (if i = stopCount n - 1 then some (concatProduct n (stopCount n)) else none) := by
      by_cases same : i = stopCount n - 1
      · have count : i + 1 = stopCount n := by omega
        simp only [if_pos same, count, yes, if_true]
      · have no : accepted n (i + 1) = false := by
          apply Bool.eq_false_iff.mpr
          intro acceptedValue
          have equal := nine_digits_unique n (i + 1) positive
            (accepted_nine n (i + 1) acceptedValue)
          omega
        simp [same, no]
    simp only [seedValues, replace, if_pos yes]
    rw [select_unique _ (List.nodup_range (n := 9))]
    simp [List.mem_range, show stopCount n - 1 < 9 by omega]
  · have no (i : Nat) : accepted n (i + 1) = false := by
      apply Bool.eq_false_iff.mpr
      intro acceptedValue
      have equal := nine_digits_unique n (i + 1) positive (accepted_nine n (i + 1) acceptedValue)
      exact yes (equal ▸ acceptedValue)
    simp [seedValues, no, yes]

end ProjectEulerStatements.ConcatenatedProducts
