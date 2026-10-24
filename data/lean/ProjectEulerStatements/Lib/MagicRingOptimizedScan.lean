import ProjectEulerStatements.Lib.MagicRingSetValues
import ProjectEulerStatements.Lib.MagicRingRecordCalls

/-! The optimized candidate visit rejects incomplete assignments and records canonical text. -/
namespace ProjectEulerStatements.MagicRing
open FormalSW.PyAst
set_option Elab.async false

def optimizedVisit {n : Nat} (ring : Ring n) (digits : Int) (best : String) : String :=
  MagicRingRecordCalls.record
    (textFrom ring.outer ring.inner (minimumIndex ring.outer)) digits best

def innerVisit (n : Nat) (digits : Int) (best : String) (inner : List Nat) : String :=
  match pack n (derivedOuter n inner) inner with
  | some ring => optimizedVisit ring digits best
  | none => best

def innerScan (n : Nat) (digits : Int) (rows : List (List Nat)) (best : String) : String :=
  rows.foldl (innerVisit n digits) best

def selectionScan (n : Nat) (digits : Int) (selections : List (List Nat))
    (best : String) : String :=
  selections.foldl (fun current selected =>
    innerScan n digits (Permutations.rows n selected) current) best

theorem optimizedVisit_text {n : Nat} (ring : Ring n) (digits : Int) (best : String) :
    optimizedVisit ring digits best =
      MagicRingRecordCalls.record (text ring.canonicalize.outer ring.canonicalize.inner)
        digits best := by
  rw [optimizedVisit, textFrom_eq_rotated]
  rfl

theorem optimizedVisit_eq {n : Nat} (ring : Ring n) (digits : Nat) (best : String) :
    optimizedVisit ring digits best =
      if (text ring.canonicalize.outer ring.canonicalize.inner).toList.length = digits
      then max best (text ring.canonicalize.outer ring.canonicalize.inner) else best := by
  rw [optimizedVisit_text, MagicRingRecordCalls.record_max]
  simp only [Int.natCast_inj]

theorem innerScan_nil (n : Nat) (digits : Int) (best : String) :
    innerScan n digits [] best = best := rfl

theorem innerScan_cons (n : Nat) (digits : Int) (row : List Nat) (rest : List (List Nat))
    (best : String) :
    innerScan n digits (row :: rest) best =
      innerScan n digits rest (innerVisit n digits best row) := rfl

theorem innerScan_filtered (n digits : Nat) (rows : List (List Nat)) (best : String) :
    innerScan n digits rows best =
      (((rows.filterMap (fun row => pack n (derivedOuter n row) row)).filterMap (fun ring =>
        if (text ring.canonicalize.outer ring.canonicalize.inner).toList.length = digits
        then some (text ring.canonicalize.outer ring.canonicalize.inner) else none)).foldl
          max best) := by
  induction rows generalizing best with
  | nil => rfl
  | cons row rest ih =>
      rw [innerScan_cons]
      cases packed : pack n (derivedOuter n row) row with
      | none => simpa only [innerVisit, packed, List.filterMap_cons] using ih best
      | some ring =>
          by_cases width :
              (text ring.canonicalize.outer ring.canonicalize.inner).toList.length = digits
          · simpa only [innerVisit, packed, optimizedVisit_eq, width, if_true,
              List.filterMap_cons, List.foldl_cons] using
              ih (max best (text ring.canonicalize.outer ring.canonicalize.inner))
          · simpa only [innerVisit, packed, optimizedVisit_eq, width, if_false,
              List.filterMap_cons] using ih best

theorem selectionScan_filtered (n digits : Nat) (selections : List (List Nat)) (best : String) :
    selectionScan n digits selections best =
      (((selections.flatMap (fun selected =>
        (Permutations.rows n selected).filterMap (fun row =>
          pack n (derivedOuter n row) row))).filterMap
          (fun ring =>
            if (text ring.canonicalize.outer ring.canonicalize.inner).toList.length = digits
            then some (text ring.canonicalize.outer ring.canonicalize.inner) else none)).foldl
              max best) := by
  induction selections generalizing best with
  | nil => rfl
  | cons selected rest ih =>
      change selectionScan n digits rest
        (innerScan n digits (Permutations.rows n selected) best) = _
      rw [ih, innerScan_filtered]
      simp only [List.flatMap_cons, List.filterMap_append, List.foldl_append]

theorem selectionScan_answer (n digits : Nat) :
    selectionScan n digits (Combinations.rows n (labels n)) "" = optimizedAnswer n digits :=
  selectionScan_filtered n digits _ ""

theorem packed_validation (n : Nat) (positive : 0 < n) (inner : List Nat) (ring : Ring n)
    (packed : pack n (derivedOuter n inner) inner = some ring) :
    (builtOuter n inner).length = n ∧
      (IntegerSets.entries (builtOuter n inner)).length = n ∧
      ScalarSet.compare .eq (IntegerSets.entries (builtOuter n inner))
        (ScalarSet.difference (IntegerSets.entries (ints (labels n)))
          (IntegerSets.entries (ints inner))) = true := by
  obtain ⟨outer, inside⟩ := (pack_spec _ _ ring).mp packed
  have forced : ring.outer = derivedOuter n ring.inner := by rw [inside]; exact outer
  have checked := magic_validation ring positive (target n ring.inner) (derived_magic ring forced)
  simpa only [inside] using checked

theorem innerVisit_incomplete (n : Nat) (positive : 0 < n) (digits : Int)
    (best : String) (inner : List Nat) (incomplete : (builtOuter n inner).length ≠ n) :
    innerVisit n digits best inner = best := by
  unfold innerVisit
  cases packed : pack n (derivedOuter n inner) inner with
  | none => rfl
  | some ring => exact False.elim (incomplete (packed_validation n positive inner ring packed).1)

theorem innerVisit_rejected (n : Nat) (positive : 0 < n) (digits : Int)
    (best : String) (inner : List Nat)
    (rejected : ¬ (ScalarSet.compare .eq (IntegerSets.entries (builtOuter n inner))
        (ScalarSet.difference (IntegerSets.entries (ints (labels n)))
          (IntegerSets.entries (ints inner))) = true ∧
      (IntegerSets.entries (builtOuter n inner)).length = n)) :
    innerVisit n digits best inner = best := by
  unfold innerVisit
  cases packed : pack n (derivedOuter n inner) inner with
  | none => rfl
  | some ring =>
      have checked := packed_validation n positive inner ring packed
      exact False.elim (rejected ⟨checked.2.2, checked.2.1⟩)

theorem innerVisit_ring (n : Nat) (digits : Int) (best : String) (inner : List Nat)
    (ring : Ring n) (inside : ring.inner = inner)
    (forced : ring.outer = derivedOuter n ring.inner) :
    innerVisit n digits best inner = optimizedVisit ring digits best := by
  have packed : pack n (derivedOuter n inner) inner = some ring :=
    (pack_spec _ _ ring).mpr ⟨by rw [← inside]; exact forced, inside⟩
  simp only [innerVisit, packed]

theorem complement_perm (n : Nat) (left right : List Nat) (same : left.Perm right) :
    ScalarSet.difference (IntegerSets.entries (ints (labels n))) (IntegerSets.entries (ints left)) =
      ScalarSet.difference (IntegerSets.entries (ints (labels n)))
        (IntegerSets.entries (ints right)) := by
  simp only [IntegerSets.difference_entries, ints,
    (same.map (fun value : Nat => (value : Int))).mem_iff]

end ProjectEulerStatements.MagicRing
