import ProjectEulerStatements.Lib.ChampernowneBlocks

/-! A generated decimal prefix determines every position it already contains. -/
namespace ProjectEulerStatements.ChampernownePrefix
open P40 ChampernowneBlocks
set_option Elab.async false

theorem append (count rest : Nat) :
    champernowneDigits (count + rest) = champernowneDigits count ++ stream (count + 1) rest := by
  simp only [champernowneDigits_stream, stream_append, Nat.add_comm]

theorem succ (count : Nat) :
    champernowneDigits (count + 1) = champernowneDigits count ++ digitsBE (count + 1) := by
  simpa only [stream, List.range'_one, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
    append count 1

theorem digits_positive (value : Nat) (positive : 0 < value) : 0 < (digitsBE value).length := by
  rw [digitsBE, List.length_reverse]
  exact List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega))

/-- Every positive integer contributes at least one digit. -/
theorem length_lower (count : Nat) : count ≤ (champernowneDigits count).length := by
  induction count with
  | zero => simp [champernowneDigits]
  | succ count ih =>
      rw [succ, List.length_append]
      have contributes := digits_positive (count + 1) (by omega)
      omega

theorem get_stable (left right index : Nat) (ordered : left ≤ right)
    (inside : index < (champernowneDigits left).length) :
    (champernowneDigits right).getD index 0 = (champernowneDigits left).getD index 0 := by
  have split : right = left + (right - left) := by omega
  rw [split, append, List.getD_append _ _ _ _ inside]

/-- Stopping when the requested digit exists suffices; no integer-count cutoff is required. -/
theorem digit_complete (position count : Nat) (positive : 0 < position)
    (covered : position ≤ (champernowneDigits count).length) :
    (champernowneDigits count).getD (position - 1) 0 = blockDigit 1 position := by
  rw [blockDigit_correct position position positive (Nat.le_refl _), digitAt]
  by_cases ordered : count ≤ position
  · exact (get_stable count position (position - 1) ordered (by omega)).symm
  · apply get_stable position count (position - 1) (by omega)
    have enough := length_lower position
    omega

end ProjectEulerStatements.ChampernownePrefix
