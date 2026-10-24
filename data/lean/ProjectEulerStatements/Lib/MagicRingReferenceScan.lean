import ProjectEulerStatements.Lib.MagicRingSearch
import ProjectEulerStatements.Lib.MagicRingRecordCalls

/-! The reference's running maximum folds the complete assignment enumeration. -/
namespace ProjectEulerStatements.MagicRing
set_option Elab.async false

def referenceVisit {n : Nat} (ring : Ring n) (digits : Int) (best : String) : String :=
  if Canonical ring ∧ Magic ring (firstSum ring)
  then MagicRingRecordCalls.record (text ring.outer ring.inner) digits best else best

def rowVisit (n : Nat) (digits : Int) (best : String) (row : List Nat) : String :=
  match pack n (row.take n) (row.drop n) with
  | some ring => referenceVisit ring digits best
  | none => best

def referenceScan (n : Nat) (digits : Int) (rows : List (List Nat)) (best : String) : String :=
  rows.foldl (rowVisit n digits) best

def referenceResult (n digits : Int) : String :=
  if n < 3 ∨ digits < 3 * n then "" else referenceAnswer n.toNat digits.toNat

theorem referenceVisit_eq {n : Nat} (ring : Ring n) (digits : Nat) (best : String) :
    referenceVisit ring digits best =
      if Canonical ring ∧ Magic ring (firstSum ring) ∧
          (text ring.outer ring.inner).toList.length = digits
      then max best (text ring.outer ring.inner) else best := by
  by_cases good : Canonical ring ∧ Magic ring (firstSum ring)
  · simp only [referenceVisit, MagicRingRecordCalls.record_max, Int.natCast_inj,
      good.1, good.2, true_and, if_true]
  · have rejected : ¬ (Canonical ring ∧ Magic ring (firstSum ring) ∧
        (text ring.outer ring.inner).toList.length = digits) :=
      fun accepted => good ⟨accepted.1, accepted.2.1⟩
    rw [referenceVisit, if_neg good, if_neg rejected]

theorem referenceScan_nil (n : Nat) (digits : Int) (best : String) :
    referenceScan n digits [] best = best := rfl

theorem referenceScan_cons (n : Nat) (digits : Int) (row : List Nat)
    (rest : List (List Nat)) (best : String) :
    referenceScan n digits (row :: rest) best =
      referenceScan n digits rest (rowVisit n digits best row) := rfl

theorem referenceScan_filtered (n digits : Nat) (rows : List (List Nat)) (best : String) :
    referenceScan n digits rows best =
      (((rows.filterMap (fun row => pack n (row.take n) (row.drop n))).filterMap (fun ring =>
        if Canonical ring ∧ Magic ring (firstSum ring) ∧
            (text ring.outer ring.inner).toList.length = digits
        then some (text ring.outer ring.inner) else none)).foldl max best) := by
  induction rows generalizing best with
  | nil => rfl
  | cons row rest ih =>
      rw [referenceScan_cons]
      cases packed : pack n (row.take n) (row.drop n) with
      | none => simpa only [rowVisit, packed, List.filterMap_cons] using ih best
      | some ring =>
          by_cases accepted : Canonical ring ∧ Magic ring (firstSum ring) ∧
              (text ring.outer ring.inner).toList.length = digits
          · simpa only [rowVisit, packed, referenceVisit_eq, accepted, if_true,
              List.filterMap_cons, List.foldl_cons] using ih (max best (text ring.outer ring.inner))
          · simpa only [rowVisit, packed, referenceVisit_eq, accepted, if_false,
              List.filterMap_cons] using ih best

theorem referenceScan_answer (n digits : Nat) :
    referenceScan n digits (FormalSW.PyAst.Permutations.rows (2 * n) (labels n)) "" =
      referenceAnswer n digits := referenceScan_filtered n digits _ ""

theorem pack_assignment (n : Nat) (row : List Nat) (assignment : row.Perm (labels n)) :
    ∃ ring : Ring n, pack n (row.take n) (row.drop n) = some ring ∧
      ring.outer ++ ring.inner = row := by
  have length : row.length = 2 * n := by simpa [labels] using assignment.length_eq
  have outerSize : (row.take n).length = n := by simp [List.length_take, length]; omega
  have innerSize : (row.drop n).length = n := by simp [List.length_drop, length]; omega
  let ring : Ring n := ⟨row.take n, row.drop n, outerSize, innerSize,
    by simpa only [List.take_append_drop] using assignment⟩
  exact ⟨ring, pack_self ring, List.take_append_drop n row⟩

end ProjectEulerStatements.MagicRing
