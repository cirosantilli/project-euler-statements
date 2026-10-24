import ProjectEulerStatements.P40
import ProjectEulerStatements.Lib.UniformBlocks
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega

/-! Lookup in Champernowne's decimal blocks without constructing a digit prefix. -/
namespace ProjectEulerStatements.ChampernowneBlocks
open P40

set_option Elab.async false

def stream (first count : Nat) : List Nat :=
  (List.range' first count).flatMap digitsBE

private theorem collect_digits (items : List Nat) (before : List Nat) :
    items.foldl (fun acc i => acc ++ digitsBE (i + 1)) before =
      before ++ items.flatMap (fun i => digitsBE (i + 1)) := by
  induction items generalizing before with
  | nil => simp
  | cons head tail ih => simp [ih, List.append_assoc]

theorem champernowneDigits_stream (limit : Nat) : champernowneDigits limit = stream 1 limit := by
  simp only [champernowneDigits, collect_digits, List.nil_append, stream,
    List.range'_eq_map_range, List.flatMap_map, Nat.add_comm]

theorem stream_append (first count rest : Nat) :
    stream first (count + rest) = stream first count ++ stream (first + count) rest := by
  rw [stream, ← List.range'_append_1, List.flatMap_append]
  rfl

@[simp] theorem stream_zero (first : Nat) : stream first 0 = [] := rfl

def blockStart (width : Nat) : Nat := 10 ^ (width - 1)
def blockCount (width : Nat) : Nat := 9 * blockStart width
def blockSize (width : Nat) : Nat := blockCount width * width

theorem blockStart_positive (width : Nat) : 0 < blockStart width := Nat.pow_pos (by decide)

theorem blockCount_positive (width : Nat) : 0 < blockCount width :=
  Nat.mul_pos (by decide) (blockStart_positive width)

theorem blockSize_positive (width : Nat) (positive : 0 < width) : 0 < blockSize width :=
  Nat.mul_pos (blockCount_positive width) positive

theorem next_start (width : Nat) (positive : 0 < width) :
    blockStart (width + 1) = blockStart width * 10 := by
  have exponent : width = (width - 1) + 1 := by omega
  simp only [blockStart, Nat.add_sub_cancel]
  exact (congrArg (fun n : Nat => 10 ^ n) exponent).trans (Nat.pow_succ 10 (width - 1))

theorem next_count (width : Nat) (positive : 0 < width) :
    blockCount (width + 1) = blockCount width * 10 := by
  rw [blockCount, next_start width positive]
  simp only [blockCount, Nat.mul_assoc]

theorem next_boundary (width : Nat) (positive : 0 < width) :
    blockStart width + blockCount width = blockStart (width + 1) := by
  rw [next_start width positive]
  simp only [blockCount]
  omega

theorem decimal_length (width number : Nat) (positive : 0 < width)
    (lower : blockStart width ≤ number)
    (upper : number < blockStart width + blockCount width) :
    (digitsBE number).length = width := by
  have above : width - 1 < (Nat.digits 10 number).length :=
    (Nat.lt_digits_length_iff (b := 10) (by decide) number).mpr lower
  have below : (Nat.digits 10 number).length ≤ width := by
    apply (Nat.digits_length_le_iff (by decide) number).mpr
    rw [next_boundary width positive] at upper
    simpa only [blockStart, Nat.add_sub_cancel] using upper
  simpa only [digitsBE, List.length_reverse] using
    (show (Nat.digits 10 number).length = width by omega)

/-- Width zero is a harmless totalization; every actual source state has positive width. -/
def blockDigit (width rank : Nat) : Nat :=
  if continued : 0 < width ∧ blockSize width < rank then
    blockDigit (width + 1) (rank - blockSize width)
  else
    (digitsBE (blockStart width + (rank - 1) / width)).getD ((rank - 1) % width) 0
termination_by rank
decreasing_by exact Nat.sub_lt (by omega) (blockSize_positive width continued.1)

theorem blockDigit_step (width rank : Nat) (positive : 0 < width) :
    blockDigit width rank =
      if blockSize width < rank then blockDigit (width + 1) (rank - blockSize width)
      else (digitsBE (blockStart width + (rank - 1) / width)).getD ((rank - 1) % width) 0 := by
  rw [blockDigit]
  by_cases skip : blockSize width < rank <;> simp [positive, skip]

/- Append inside ChampernowneBlocks; import ProjectEulerStatements.Lib.UniformBlocks. -/
private theorem uniform_digits (width count : Nat) (positive : 0 < width)
    (bounded : count ≤ blockCount width) :
    ∀ n ∈ List.range' (blockStart width) count, (digitsBE n).length = width := by
  intro n member
  obtain ⟨index, inside, equal⟩ := List.mem_range'.mp member
  simp only [Nat.one_mul] at equal
  apply decimal_length width n positive <;> omega

theorem block_prefix_length (width count : Nat) (positive : 0 < width)
    (bounded : count ≤ blockCount width) :
    (stream (blockStart width) count).length = count * width := by
  simpa only [stream, List.length_range'] using
    UniformBlocks.uniform_flatMap_length (List.range' (blockStart width) count) digitsBE width
      (uniform_digits width count positive bounded)

/-- Supplying at least rank positive integers is sufficient; a final partial
decimal block does not need to be padded or enumerated. -/
theorem blockDigit_stream (width rank count : Nat) (widthPositive : 0 < width)
    (rankPositive : 0 < rank) (covered : rank ≤ count) :
    blockDigit width rank = (stream (blockStart width) count).getD (rank - 1) 0 := by
  induction rank using Nat.strong_induction_on generalizing width count with
  | h rank ih =>
      rw [blockDigit_step width rank widthPositive]
      have blockLower : blockCount width ≤ blockSize width :=
        Nat.le_mul_of_pos_right _ widthPositive
      by_cases skip : blockSize width < rank
      · rw [if_pos skip]
        have enough : blockCount width ≤ count := by omega
        have split : stream (blockStart width) count =
            stream (blockStart width) (blockCount width) ++
              stream (blockStart width + blockCount width) (count - blockCount width) := by
          rw [← stream_append]
          congr 1
          omega
        have length : (stream (blockStart width) (blockCount width)).length = blockSize width :=
          block_prefix_length width (blockCount width) widthPositive (Nat.le_refl _)
        rw [split, List.getD_append_right _ _ _ _ (by omega), length,
          next_boundary width widthPositive]
        have offset : rank - 1 - blockSize width = (rank - blockSize width) - 1 := by omega
        rw [offset]
        exact ih (rank - blockSize width)
          (Nat.sub_lt rankPositive (blockSize_positive width widthPositive))
          (width + 1) (count - blockCount width) (by omega) (by omega) (by omega)
      · rw [if_neg skip]
        let segmentCount := min (blockCount width) count
        have segmentCountBound : segmentCount ≤ blockCount width := Nat.min_le_left _ _
        have segmentCountCount : segmentCount ≤ count := Nat.min_le_right _ _
        have inside : rank - 1 < segmentCount * width := by
          by_cases less : blockCount width ≤ count
          · have same : segmentCount = blockCount width := Nat.min_eq_left less
            rw [same]
            change rank - 1 < blockSize width
            omega
          · have same : segmentCount = count := Nat.min_eq_right (by omega)
            have lengthLower : count ≤ count * width := Nat.le_mul_of_pos_right _ widthPositive
            rw [same]
            omega
        have split : stream (blockStart width) count = stream (blockStart width) segmentCount ++
            stream (blockStart width + segmentCount) (count - segmentCount) := by
          rw [← stream_append]
          congr 1
          omega
        rw [split, List.getD_append _ _ _ _ (by
          rw [block_prefix_length width segmentCount widthPositive segmentCountBound]
          exact inside)]
        exact (UniformBlocks.uniform_range_getD (blockStart width) segmentCount width digitsBE 0
          widthPositive (uniform_digits width segmentCount widthPositive segmentCountBound)
          (rank - 1) inside).symm

/-- The optimized algorithm agrees with every sufficiently long finite reference stream. -/
theorem blockDigit_correct (rank limit : Nat) (positive : 0 < rank) (bounded : rank ≤ limit) :
    blockDigit 1 rank = P40.digitAt rank limit := by
  have calculated := blockDigit_stream 1 rank limit (by decide) positive bounded
  simpa only [P40.digitAt, champernowneDigits_stream, blockStart, Nat.sub_self, Nat.pow_zero]
    using calculated

end ProjectEulerStatements.ChampernowneBlocks
