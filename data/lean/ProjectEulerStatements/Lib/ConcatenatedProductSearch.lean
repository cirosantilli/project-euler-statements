import ProjectEulerStatements.Lib.ConcatenatedProductCandidates

/-! Per-seed uniqueness turns the reference list maximum into the optimized running maximum. -/
namespace ProjectEulerStatements.ConcatenatedProducts

open P38

theorem accepted_eq (n k : Nat) :
    accepted n k = (decide (1 < k) && isPandigital1to9 (concatProduct n k)) := by
  by_cases nine : numDigits (concatProduct n k) = 9
  · simp [accepted, nine]
  · have absent : (digitsBE (concatProduct n k)).length ≠ 9 := by
      simpa only [digitsBE, List.length_reverse, numDigits] using nine
    have rejected : isPandigital1to9 (concatProduct n k) = false := by
      simp [isPandigital1to9, absent]
    simp [accepted, nine, rejected]

noncomputable def seedScore (n : Nat) : Nat :=
  if accepted n (stopCount n) then concatProduct n (stopCount n) else 0

noncomputable def scan (first count best : Nat) : Nat :=
  (List.range' first count).foldl (fun best n => max best (seedScore n)) best

theorem seed_fold (n best : Nat) (positive : 0 < n) :
    (seedValues n).foldl Nat.max best = max best (seedScore n) := by
  rw [seedValues_at_stop n positive]
  cases yes : accepted n (stopCount n) <;> simp [yes, seedScore]

theorem candidates_fold (items : List Nat) (best : Nat)
    (positive : ∀ n ∈ items, 0 < n) :
    (items.flatMap seedValues).foldl Nat.max best =
      items.foldl (fun best n => max best (seedScore n)) best := by
  induction items generalizing best with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons, List.foldl_append, seed_fold head best (positive head (by simp))]
      exact ih _ (fun n member => positive n (by simp [member]))

theorem reference_scan (limit : Nat) : naive limit = scan 1 limit 0 := by
  rw [naive_candidates]
  simp only [List.range_eq_range', List.range'_succ, List.flatMap_cons, seedValues_zero,
    List.nil_append, listMax]
  apply candidates_fold
  intro n member
  obtain ⟨i, _, equal⟩ := List.mem_range'.mp member
  omega

theorem scan_zero (first best : Nat) : scan first 0 best = best := rfl

theorem scan_succ (first count best : Nat) :
    scan first (count + 1) best = scan (first + 1) count (max best (seedScore first)) := by
  simp only [scan, List.range'_succ, List.foldl_cons]

end ProjectEulerStatements.ConcatenatedProducts
