import ProjectEulerStatements.Lib.MagicRingOptimizedScan

/-! Width and line-sum divisibility filters preserve the complete optimized search. -/
namespace ProjectEulerStatements.MagicRing
open FormalSW.PyAst
set_option Elab.async false

def requiredDigits (n : Nat) (inner : List Nat) : Nat :=
  ((labels n).map digitWidth).sum + (inner.map digitWidth).sum

def SelectionAdmissible (n : Nat) (digits : Int) (inner : List Nat) : Prop :=
  (requiredDigits n inner : Int) = digits ∧ (n * (2 * n + 1) + inner.sum) % n = 0

instance (n : Nat) (digits : Int) (inner : List Nat) :
    Decidable (SelectionAdmissible n digits inner) := by
  unfold SelectionAdmissible
  infer_instance

def selectionVisit (n : Nat) (digits : Int) (best : String) (selected : List Nat) : String :=
  if SelectionAdmissible n digits selected
  then innerScan n digits (Permutations.rows n selected) best else best

def prunedSelectionScan (n : Nat) (digits : Int) (selections : List (List Nat))
    (best : String) : String := selections.foldl (selectionVisit n digits) best

theorem canonical_text_length {n : Nat} (ring : Ring n) :
    (text ring.canonicalize.outer ring.canonicalize.inner).toList.length =
      requiredDigits n ring.inner := by
  rw [text_length]
  change _ + ((ring.inner.rotate (minimumIndex ring.outer)).map digitWidth).sum = _
  rw [((List.rotate_perm ring.inner (minimumIndex ring.outer)).map digitWidth).sum_eq]
  rfl

theorem innerVisit_wrong_width (n : Nat) (digits : Int) (best : String) (inner : List Nat)
    (wrong : (requiredDigits n inner : Int) ≠ digits) : innerVisit n digits best inner = best := by
  unfold innerVisit
  cases packed : pack n (derivedOuter n inner) inner with
  | none => rfl
  | some ring =>
      have inside := ((pack_spec _ _ ring).mp packed).2
      have width := canonical_text_length ring
      rw [inside] at width
      change optimizedVisit ring digits best = best
      rw [optimizedVisit_text, MagicRingRecordCalls.record_max, width, if_neg wrong]

theorem innerVisit_not_divisible (n : Nat) (digits : Int) (best : String) (inner : List Nat)
    (wrong : (n * (2 * n + 1) + inner.sum) % n ≠ 0) : innerVisit n digits best inner = best := by
  unfold innerVisit
  cases packed : pack n (derivedOuter n inner) inner with
  | none => rfl
  | some ring =>
      obtain ⟨outer, inside⟩ := (pack_spec _ _ ring).mp packed
      have forced : ring.outer = derivedOuter n ring.inner := by rw [inside]; exact outer
      have divisible := sum_mod_eq_zero ring (target n ring.inner) (derived_magic ring forced)
      exact False.elim (wrong (by simpa only [inside] using divisible))

theorem innerScan_fixed (n : Nat) (digits : Int) (rows : List (List Nat))
    (fixed : ∀ row ∈ rows, ∀ best, innerVisit n digits best row = best) (best : String) :
    innerScan n digits rows best = best := by
  induction rows generalizing best with
  | nil => rfl
  | cons row rest ih =>
      rw [innerScan_cons, fixed row List.mem_cons_self best]
      exact ih (fun entry member => fixed entry (List.mem_cons_of_mem _ member)) best

theorem selection_rejected (n : Nat) (digits : Int) (selected : List Nat)
    (size : selected.length = n) (rejected : ¬ SelectionAdmissible n digits selected)
    (best : String) : innerScan n digits (Permutations.rows n selected) best = best := by
  apply innerScan_fixed
  intro row member current
  have same := Permutations.row_perm n selected row size member
  by_cases width : (requiredDigits n selected : Int) = digits
  · apply innerVisit_not_divisible
    have wrong : (n * (2 * n + 1) + selected.sum) % n ≠ 0 :=
      fun divisible => rejected ⟨width, divisible⟩
    simpa only [same.sum_eq] using wrong
  · apply innerVisit_wrong_width
    simpa only [requiredDigits, (same.map digitWidth).sum_eq] using width

theorem selectionVisit_unpruned (n : Nat) (digits : Int) (best : String) (selected : List Nat)
    (size : selected.length = n) :
    selectionVisit n digits best selected =
      innerScan n digits (Permutations.rows n selected) best := by
  unfold selectionVisit
  split
  · rfl
  · exact (selection_rejected n digits selected size (by assumption) best).symm

theorem prunedSelectionScan_eq (n : Nat) (digits : Int) (selections : List (List Nat))
    (valid : ∀ selected ∈ selections, selected.length = n) (best : String) :
    prunedSelectionScan n digits selections best = selectionScan n digits selections best := by
  induction selections generalizing best with
  | nil => rfl
  | cons selected rest ih =>
      change prunedSelectionScan n digits rest (selectionVisit n digits best selected) = _
      rw [selectionVisit_unpruned n digits best selected (valid selected List.mem_cons_self)]
      exact ih (fun entry member => valid entry (List.mem_cons_of_mem _ member)) _

theorem prunedSelectionScan_answer (n digits : Nat) :
    prunedSelectionScan n digits (Combinations.rows n (labels n)) "" =
      optimizedAnswer n digits := by
  rw [prunedSelectionScan_eq n digits _
    (fun selected member => ((Combinations.mem_rows_iff _ _ _).mp member).2),
    selectionScan_answer]

end ProjectEulerStatements.MagicRing
