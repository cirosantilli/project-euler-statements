import ProjectEulerStatements.Lib.PandigitalProducts

/-! Bounded kernel checks for both pandigital searches after decimal-length reduction.
Each check covers at most 250 candidates; elaboration is serial to limit memory. -/
namespace ProjectEulerStatements.PandigitalCertificate
open PandigitalProducts

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def referenceChunk (a first count : Nat) : List Nat :=
  ((List.range' first count).filter (P32.pandigitalProduct a)).map (a * ·)

private def optimizedChunk (a first count : Nat) : List Nat :=
  ((List.range' first count).filter (accepted a)).map (a * ·)

private theorem referenceChunk_append (a first left right : Nat) :
    referenceChunk a first (left + right) = referenceChunk a first left ++ referenceChunk a (first + left) right := by
  unfold referenceChunk
  rw [← List.range'_append_1]
  simp only [List.filter_append, List.map_append]

private theorem optimizedChunk_append (a first left right : Nat) :
    optimizedChunk a first (left + right) = optimizedChunk a first left ++ optimizedChunk a (first + left) right := by
  unfold optimizedChunk
  rw [← List.range'_append_1]
  simp only [List.filter_append, List.map_append]

private theorem reference_1_0 : referenceChunk 1 1000 250 = [] := by decide +kernel
private theorem reference_1_1 : referenceChunk 1 1250 250 = [] := by decide +kernel
private theorem reference_1_2 : referenceChunk 1 1500 250 = [] := by decide +kernel
private theorem reference_1_3 : referenceChunk 1 1750 250 = [] := by decide +kernel
private theorem reference_1_4 : referenceChunk 1 2000 250 = [] := by decide +kernel
private theorem reference_1_5 : referenceChunk 1 2250 250 = [] := by decide +kernel
private theorem reference_1_6 : referenceChunk 1 2500 250 = [] := by decide +kernel
private theorem reference_1_7 : referenceChunk 1 2750 250 = [] := by decide +kernel
private theorem reference_1_8 : referenceChunk 1 3000 250 = [] := by decide +kernel
private theorem reference_1_9 : referenceChunk 1 3250 250 = [] := by decide +kernel
private theorem reference_1_10 : referenceChunk 1 3500 250 = [] := by decide +kernel
private theorem reference_1_11 : referenceChunk 1 3750 250 = [] := by decide +kernel
private theorem reference_1_12 : referenceChunk 1 4000 250 = [] := by decide +kernel
private theorem reference_1_13 : referenceChunk 1 4250 250 = [] := by decide +kernel
private theorem reference_1_14 : referenceChunk 1 4500 250 = [] := by decide +kernel
private theorem reference_1_15 : referenceChunk 1 4750 250 = [] := by decide +kernel
private theorem reference_1_16 : referenceChunk 1 5000 250 = [] := by decide +kernel
private theorem reference_1_17 : referenceChunk 1 5250 250 = [] := by decide +kernel
private theorem reference_1_18 : referenceChunk 1 5500 250 = [] := by decide +kernel
private theorem reference_1_19 : referenceChunk 1 5750 250 = [] := by decide +kernel
private theorem reference_1_20 : referenceChunk 1 6000 250 = [] := by decide +kernel
private theorem reference_1_21 : referenceChunk 1 6250 250 = [] := by decide +kernel
private theorem reference_1_22 : referenceChunk 1 6500 250 = [] := by decide +kernel
private theorem reference_1_23 : referenceChunk 1 6750 250 = [] := by decide +kernel
private theorem reference_1_24 : referenceChunk 1 7000 250 = [] := by decide +kernel
private theorem reference_1_25 : referenceChunk 1 7250 250 = [] := by decide +kernel
private theorem reference_1_26 : referenceChunk 1 7500 250 = [] := by decide +kernel
private theorem reference_1_27 : referenceChunk 1 7750 250 = [] := by decide +kernel
private theorem reference_1_28 : referenceChunk 1 8000 250 = [] := by decide +kernel
private theorem reference_1_29 : referenceChunk 1 8250 250 = [] := by decide +kernel
private theorem reference_1_30 : referenceChunk 1 8500 250 = [] := by decide +kernel
private theorem reference_1_31 : referenceChunk 1 8750 250 = [] := by decide +kernel
private theorem reference_1_32 : referenceChunk 1 9000 250 = [] := by decide +kernel
private theorem reference_1_33 : referenceChunk 1 9250 250 = [] := by decide +kernel
private theorem reference_1_34 : referenceChunk 1 9500 250 = [] := by decide +kernel
private theorem reference_1_35 : referenceChunk 1 9750 250 = [] := by decide +kernel

private theorem reference_row1 : referenceChunk 1 (lowerBound 1000 1) (upperBound 9999 1 + 1 - lowerBound 1000 1) = [] := by
  change referenceChunk 1 1000 9000 = _
  rewrite [referenceChunk_append 1 1000 250 8750]
  rewrite [reference_1_0]
  rewrite [referenceChunk_append 1 1250 250 8500]
  rewrite [reference_1_1]
  rewrite [referenceChunk_append 1 1500 250 8250]
  rewrite [reference_1_2]
  rewrite [referenceChunk_append 1 1750 250 8000]
  rewrite [reference_1_3]
  rewrite [referenceChunk_append 1 2000 250 7750]
  rewrite [reference_1_4]
  rewrite [referenceChunk_append 1 2250 250 7500]
  rewrite [reference_1_5]
  rewrite [referenceChunk_append 1 2500 250 7250]
  rewrite [reference_1_6]
  rewrite [referenceChunk_append 1 2750 250 7000]
  rewrite [reference_1_7]
  rewrite [referenceChunk_append 1 3000 250 6750]
  rewrite [reference_1_8]
  rewrite [referenceChunk_append 1 3250 250 6500]
  rewrite [reference_1_9]
  rewrite [referenceChunk_append 1 3500 250 6250]
  rewrite [reference_1_10]
  rewrite [referenceChunk_append 1 3750 250 6000]
  rewrite [reference_1_11]
  rewrite [referenceChunk_append 1 4000 250 5750]
  rewrite [reference_1_12]
  rewrite [referenceChunk_append 1 4250 250 5500]
  rewrite [reference_1_13]
  rewrite [referenceChunk_append 1 4500 250 5250]
  rewrite [reference_1_14]
  rewrite [referenceChunk_append 1 4750 250 5000]
  rewrite [reference_1_15]
  rewrite [referenceChunk_append 1 5000 250 4750]
  rewrite [reference_1_16]
  rewrite [referenceChunk_append 1 5250 250 4500]
  rewrite [reference_1_17]
  rewrite [referenceChunk_append 1 5500 250 4250]
  rewrite [reference_1_18]
  rewrite [referenceChunk_append 1 5750 250 4000]
  rewrite [reference_1_19]
  rewrite [referenceChunk_append 1 6000 250 3750]
  rewrite [reference_1_20]
  rewrite [referenceChunk_append 1 6250 250 3500]
  rewrite [reference_1_21]
  rewrite [referenceChunk_append 1 6500 250 3250]
  rewrite [reference_1_22]
  rewrite [referenceChunk_append 1 6750 250 3000]
  rewrite [reference_1_23]
  rewrite [referenceChunk_append 1 7000 250 2750]
  rewrite [reference_1_24]
  rewrite [referenceChunk_append 1 7250 250 2500]
  rewrite [reference_1_25]
  rewrite [referenceChunk_append 1 7500 250 2250]
  rewrite [reference_1_26]
  rewrite [referenceChunk_append 1 7750 250 2000]
  rewrite [reference_1_27]
  rewrite [referenceChunk_append 1 8000 250 1750]
  rewrite [reference_1_28]
  rewrite [referenceChunk_append 1 8250 250 1500]
  rewrite [reference_1_29]
  rewrite [referenceChunk_append 1 8500 250 1250]
  rewrite [reference_1_30]
  rewrite [referenceChunk_append 1 8750 250 1000]
  rewrite [reference_1_31]
  rewrite [referenceChunk_append 1 9000 250 750]
  rewrite [reference_1_32]
  rewrite [referenceChunk_append 1 9250 250 500]
  rewrite [reference_1_33]
  rewrite [referenceChunk_append 1 9500 250 250]
  rewrite [reference_1_34]
  rewrite [reference_1_35]
  rfl

private theorem optimized_1_0 : optimizedChunk 1 1000 250 = [] := by decide +kernel
private theorem optimized_1_1 : optimizedChunk 1 1250 250 = [] := by decide +kernel
private theorem optimized_1_2 : optimizedChunk 1 1500 250 = [] := by decide +kernel
private theorem optimized_1_3 : optimizedChunk 1 1750 250 = [] := by decide +kernel
private theorem optimized_1_4 : optimizedChunk 1 2000 250 = [] := by decide +kernel
private theorem optimized_1_5 : optimizedChunk 1 2250 250 = [] := by decide +kernel
private theorem optimized_1_6 : optimizedChunk 1 2500 250 = [] := by decide +kernel
private theorem optimized_1_7 : optimizedChunk 1 2750 250 = [] := by decide +kernel
private theorem optimized_1_8 : optimizedChunk 1 3000 250 = [] := by decide +kernel
private theorem optimized_1_9 : optimizedChunk 1 3250 250 = [] := by decide +kernel
private theorem optimized_1_10 : optimizedChunk 1 3500 250 = [] := by decide +kernel
private theorem optimized_1_11 : optimizedChunk 1 3750 250 = [] := by decide +kernel
private theorem optimized_1_12 : optimizedChunk 1 4000 250 = [] := by decide +kernel
private theorem optimized_1_13 : optimizedChunk 1 4250 250 = [] := by decide +kernel
private theorem optimized_1_14 : optimizedChunk 1 4500 250 = [] := by decide +kernel
private theorem optimized_1_15 : optimizedChunk 1 4750 250 = [] := by decide +kernel
private theorem optimized_1_16 : optimizedChunk 1 5000 250 = [] := by decide +kernel
private theorem optimized_1_17 : optimizedChunk 1 5250 250 = [] := by decide +kernel
private theorem optimized_1_18 : optimizedChunk 1 5500 250 = [] := by decide +kernel
private theorem optimized_1_19 : optimizedChunk 1 5750 250 = [] := by decide +kernel
private theorem optimized_1_20 : optimizedChunk 1 6000 250 = [] := by decide +kernel
private theorem optimized_1_21 : optimizedChunk 1 6250 250 = [] := by decide +kernel
private theorem optimized_1_22 : optimizedChunk 1 6500 250 = [] := by decide +kernel
private theorem optimized_1_23 : optimizedChunk 1 6750 250 = [] := by decide +kernel
private theorem optimized_1_24 : optimizedChunk 1 7000 250 = [] := by decide +kernel
private theorem optimized_1_25 : optimizedChunk 1 7250 250 = [] := by decide +kernel
private theorem optimized_1_26 : optimizedChunk 1 7500 250 = [] := by decide +kernel
private theorem optimized_1_27 : optimizedChunk 1 7750 250 = [] := by decide +kernel
private theorem optimized_1_28 : optimizedChunk 1 8000 250 = [] := by decide +kernel
private theorem optimized_1_29 : optimizedChunk 1 8250 250 = [] := by decide +kernel
private theorem optimized_1_30 : optimizedChunk 1 8500 250 = [] := by decide +kernel
private theorem optimized_1_31 : optimizedChunk 1 8750 250 = [] := by decide +kernel
private theorem optimized_1_32 : optimizedChunk 1 9000 250 = [] := by decide +kernel
private theorem optimized_1_33 : optimizedChunk 1 9250 250 = [] := by decide +kernel
private theorem optimized_1_34 : optimizedChunk 1 9500 250 = [] := by decide +kernel
private theorem optimized_1_35 : optimizedChunk 1 9750 250 = [] := by decide +kernel

private theorem optimized_row1 : row 1000 9999 1 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 1).1 < 0 by decide +kernel)]
  change optimizedChunk 1 1000 9000 = _
  rewrite [optimizedChunk_append 1 1000 250 8750]
  rewrite [optimized_1_0]
  rewrite [optimizedChunk_append 1 1250 250 8500]
  rewrite [optimized_1_1]
  rewrite [optimizedChunk_append 1 1500 250 8250]
  rewrite [optimized_1_2]
  rewrite [optimizedChunk_append 1 1750 250 8000]
  rewrite [optimized_1_3]
  rewrite [optimizedChunk_append 1 2000 250 7750]
  rewrite [optimized_1_4]
  rewrite [optimizedChunk_append 1 2250 250 7500]
  rewrite [optimized_1_5]
  rewrite [optimizedChunk_append 1 2500 250 7250]
  rewrite [optimized_1_6]
  rewrite [optimizedChunk_append 1 2750 250 7000]
  rewrite [optimized_1_7]
  rewrite [optimizedChunk_append 1 3000 250 6750]
  rewrite [optimized_1_8]
  rewrite [optimizedChunk_append 1 3250 250 6500]
  rewrite [optimized_1_9]
  rewrite [optimizedChunk_append 1 3500 250 6250]
  rewrite [optimized_1_10]
  rewrite [optimizedChunk_append 1 3750 250 6000]
  rewrite [optimized_1_11]
  rewrite [optimizedChunk_append 1 4000 250 5750]
  rewrite [optimized_1_12]
  rewrite [optimizedChunk_append 1 4250 250 5500]
  rewrite [optimized_1_13]
  rewrite [optimizedChunk_append 1 4500 250 5250]
  rewrite [optimized_1_14]
  rewrite [optimizedChunk_append 1 4750 250 5000]
  rewrite [optimized_1_15]
  rewrite [optimizedChunk_append 1 5000 250 4750]
  rewrite [optimized_1_16]
  rewrite [optimizedChunk_append 1 5250 250 4500]
  rewrite [optimized_1_17]
  rewrite [optimizedChunk_append 1 5500 250 4250]
  rewrite [optimized_1_18]
  rewrite [optimizedChunk_append 1 5750 250 4000]
  rewrite [optimized_1_19]
  rewrite [optimizedChunk_append 1 6000 250 3750]
  rewrite [optimized_1_20]
  rewrite [optimizedChunk_append 1 6250 250 3500]
  rewrite [optimized_1_21]
  rewrite [optimizedChunk_append 1 6500 250 3250]
  rewrite [optimized_1_22]
  rewrite [optimizedChunk_append 1 6750 250 3000]
  rewrite [optimized_1_23]
  rewrite [optimizedChunk_append 1 7000 250 2750]
  rewrite [optimized_1_24]
  rewrite [optimizedChunk_append 1 7250 250 2500]
  rewrite [optimized_1_25]
  rewrite [optimizedChunk_append 1 7500 250 2250]
  rewrite [optimized_1_26]
  rewrite [optimizedChunk_append 1 7750 250 2000]
  rewrite [optimized_1_27]
  rewrite [optimizedChunk_append 1 8000 250 1750]
  rewrite [optimized_1_28]
  rewrite [optimizedChunk_append 1 8250 250 1500]
  rewrite [optimized_1_29]
  rewrite [optimizedChunk_append 1 8500 250 1250]
  rewrite [optimized_1_30]
  rewrite [optimizedChunk_append 1 8750 250 1000]
  rewrite [optimized_1_31]
  rewrite [optimizedChunk_append 1 9000 250 750]
  rewrite [optimized_1_32]
  rewrite [optimizedChunk_append 1 9250 250 500]
  rewrite [optimized_1_33]
  rewrite [optimizedChunk_append 1 9500 250 250]
  rewrite [optimized_1_34]
  rewrite [optimized_1_35]
  rfl

private theorem reference_2_0 : referenceChunk 2 1000 250 = [] := by decide +kernel
private theorem reference_2_1 : referenceChunk 2 1250 250 = [] := by decide +kernel
private theorem reference_2_2 : referenceChunk 2 1500 250 = [] := by decide +kernel
private theorem reference_2_3 : referenceChunk 2 1750 250 = [] := by decide +kernel
private theorem reference_2_4 : referenceChunk 2 2000 250 = [] := by decide +kernel
private theorem reference_2_5 : referenceChunk 2 2250 250 = [] := by decide +kernel
private theorem reference_2_6 : referenceChunk 2 2500 250 = [] := by decide +kernel
private theorem reference_2_7 : referenceChunk 2 2750 250 = [] := by decide +kernel
private theorem reference_2_8 : referenceChunk 2 3000 250 = [] := by decide +kernel
private theorem reference_2_9 : referenceChunk 2 3250 250 = [] := by decide +kernel
private theorem reference_2_10 : referenceChunk 2 3500 250 = [] := by decide +kernel
private theorem reference_2_11 : referenceChunk 2 3750 250 = [] := by decide +kernel
private theorem reference_2_12 : referenceChunk 2 4000 250 = [] := by decide +kernel
private theorem reference_2_13 : referenceChunk 2 4250 250 = [] := by decide +kernel
private theorem reference_2_14 : referenceChunk 2 4500 250 = [] := by decide +kernel
private theorem reference_2_15 : referenceChunk 2 4750 250 = [] := by decide +kernel

private theorem reference_row2 : referenceChunk 2 (lowerBound 1000 2) (upperBound 9999 2 + 1 - lowerBound 1000 2) = [] := by
  change referenceChunk 2 1000 4000 = _
  rewrite [referenceChunk_append 2 1000 250 3750]
  rewrite [reference_2_0]
  rewrite [referenceChunk_append 2 1250 250 3500]
  rewrite [reference_2_1]
  rewrite [referenceChunk_append 2 1500 250 3250]
  rewrite [reference_2_2]
  rewrite [referenceChunk_append 2 1750 250 3000]
  rewrite [reference_2_3]
  rewrite [referenceChunk_append 2 2000 250 2750]
  rewrite [reference_2_4]
  rewrite [referenceChunk_append 2 2250 250 2500]
  rewrite [reference_2_5]
  rewrite [referenceChunk_append 2 2500 250 2250]
  rewrite [reference_2_6]
  rewrite [referenceChunk_append 2 2750 250 2000]
  rewrite [reference_2_7]
  rewrite [referenceChunk_append 2 3000 250 1750]
  rewrite [reference_2_8]
  rewrite [referenceChunk_append 2 3250 250 1500]
  rewrite [reference_2_9]
  rewrite [referenceChunk_append 2 3500 250 1250]
  rewrite [reference_2_10]
  rewrite [referenceChunk_append 2 3750 250 1000]
  rewrite [reference_2_11]
  rewrite [referenceChunk_append 2 4000 250 750]
  rewrite [reference_2_12]
  rewrite [referenceChunk_append 2 4250 250 500]
  rewrite [reference_2_13]
  rewrite [referenceChunk_append 2 4500 250 250]
  rewrite [reference_2_14]
  rewrite [reference_2_15]
  rfl

private theorem optimized_2_0 : optimizedChunk 2 1000 250 = [] := by decide +kernel
private theorem optimized_2_1 : optimizedChunk 2 1250 250 = [] := by decide +kernel
private theorem optimized_2_2 : optimizedChunk 2 1500 250 = [] := by decide +kernel
private theorem optimized_2_3 : optimizedChunk 2 1750 250 = [] := by decide +kernel
private theorem optimized_2_4 : optimizedChunk 2 2000 250 = [] := by decide +kernel
private theorem optimized_2_5 : optimizedChunk 2 2250 250 = [] := by decide +kernel
private theorem optimized_2_6 : optimizedChunk 2 2500 250 = [] := by decide +kernel
private theorem optimized_2_7 : optimizedChunk 2 2750 250 = [] := by decide +kernel
private theorem optimized_2_8 : optimizedChunk 2 3000 250 = [] := by decide +kernel
private theorem optimized_2_9 : optimizedChunk 2 3250 250 = [] := by decide +kernel
private theorem optimized_2_10 : optimizedChunk 2 3500 250 = [] := by decide +kernel
private theorem optimized_2_11 : optimizedChunk 2 3750 250 = [] := by decide +kernel
private theorem optimized_2_12 : optimizedChunk 2 4000 250 = [] := by decide +kernel
private theorem optimized_2_13 : optimizedChunk 2 4250 250 = [] := by decide +kernel
private theorem optimized_2_14 : optimizedChunk 2 4500 250 = [] := by decide +kernel
private theorem optimized_2_15 : optimizedChunk 2 4750 250 = [] := by decide +kernel

private theorem optimized_row2 : row 1000 9999 2 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 2).1 < 0 by decide +kernel)]
  change optimizedChunk 2 1000 4000 = _
  rewrite [optimizedChunk_append 2 1000 250 3750]
  rewrite [optimized_2_0]
  rewrite [optimizedChunk_append 2 1250 250 3500]
  rewrite [optimized_2_1]
  rewrite [optimizedChunk_append 2 1500 250 3250]
  rewrite [optimized_2_2]
  rewrite [optimizedChunk_append 2 1750 250 3000]
  rewrite [optimized_2_3]
  rewrite [optimizedChunk_append 2 2000 250 2750]
  rewrite [optimized_2_4]
  rewrite [optimizedChunk_append 2 2250 250 2500]
  rewrite [optimized_2_5]
  rewrite [optimizedChunk_append 2 2500 250 2250]
  rewrite [optimized_2_6]
  rewrite [optimizedChunk_append 2 2750 250 2000]
  rewrite [optimized_2_7]
  rewrite [optimizedChunk_append 2 3000 250 1750]
  rewrite [optimized_2_8]
  rewrite [optimizedChunk_append 2 3250 250 1500]
  rewrite [optimized_2_9]
  rewrite [optimizedChunk_append 2 3500 250 1250]
  rewrite [optimized_2_10]
  rewrite [optimizedChunk_append 2 3750 250 1000]
  rewrite [optimized_2_11]
  rewrite [optimizedChunk_append 2 4000 250 750]
  rewrite [optimized_2_12]
  rewrite [optimizedChunk_append 2 4250 250 500]
  rewrite [optimized_2_13]
  rewrite [optimizedChunk_append 2 4500 250 250]
  rewrite [optimized_2_14]
  rewrite [optimized_2_15]
  rfl

private theorem reference_3_0 : referenceChunk 3 1000 250 = [] := by decide +kernel
private theorem reference_3_1 : referenceChunk 3 1250 250 = [] := by decide +kernel
private theorem reference_3_2 : referenceChunk 3 1500 250 = [] := by decide +kernel
private theorem reference_3_3 : referenceChunk 3 1750 250 = [] := by decide +kernel
private theorem reference_3_4 : referenceChunk 3 2000 250 = [] := by decide +kernel
private theorem reference_3_5 : referenceChunk 3 2250 250 = [] := by decide +kernel
private theorem reference_3_6 : referenceChunk 3 2500 250 = [] := by decide +kernel
private theorem reference_3_7 : referenceChunk 3 2750 250 = [] := by decide +kernel
private theorem reference_3_8 : referenceChunk 3 3000 250 = [] := by decide +kernel
private theorem reference_3_9 : referenceChunk 3 3250 84 = [] := by decide +kernel

private theorem reference_row3 : referenceChunk 3 (lowerBound 1000 3) (upperBound 9999 3 + 1 - lowerBound 1000 3) = [] := by
  change referenceChunk 3 1000 2334 = _
  rewrite [referenceChunk_append 3 1000 250 2084]
  rewrite [reference_3_0]
  rewrite [referenceChunk_append 3 1250 250 1834]
  rewrite [reference_3_1]
  rewrite [referenceChunk_append 3 1500 250 1584]
  rewrite [reference_3_2]
  rewrite [referenceChunk_append 3 1750 250 1334]
  rewrite [reference_3_3]
  rewrite [referenceChunk_append 3 2000 250 1084]
  rewrite [reference_3_4]
  rewrite [referenceChunk_append 3 2250 250 834]
  rewrite [reference_3_5]
  rewrite [referenceChunk_append 3 2500 250 584]
  rewrite [reference_3_6]
  rewrite [referenceChunk_append 3 2750 250 334]
  rewrite [reference_3_7]
  rewrite [referenceChunk_append 3 3000 250 84]
  rewrite [reference_3_8]
  rewrite [reference_3_9]
  rfl

private theorem optimized_3_0 : optimizedChunk 3 1000 250 = [] := by decide +kernel
private theorem optimized_3_1 : optimizedChunk 3 1250 250 = [] := by decide +kernel
private theorem optimized_3_2 : optimizedChunk 3 1500 250 = [] := by decide +kernel
private theorem optimized_3_3 : optimizedChunk 3 1750 250 = [] := by decide +kernel
private theorem optimized_3_4 : optimizedChunk 3 2000 250 = [] := by decide +kernel
private theorem optimized_3_5 : optimizedChunk 3 2250 250 = [] := by decide +kernel
private theorem optimized_3_6 : optimizedChunk 3 2500 250 = [] := by decide +kernel
private theorem optimized_3_7 : optimizedChunk 3 2750 250 = [] := by decide +kernel
private theorem optimized_3_8 : optimizedChunk 3 3000 250 = [] := by decide +kernel
private theorem optimized_3_9 : optimizedChunk 3 3250 84 = [] := by decide +kernel

private theorem optimized_row3 : row 1000 9999 3 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 3).1 < 0 by decide +kernel)]
  change optimizedChunk 3 1000 2334 = _
  rewrite [optimizedChunk_append 3 1000 250 2084]
  rewrite [optimized_3_0]
  rewrite [optimizedChunk_append 3 1250 250 1834]
  rewrite [optimized_3_1]
  rewrite [optimizedChunk_append 3 1500 250 1584]
  rewrite [optimized_3_2]
  rewrite [optimizedChunk_append 3 1750 250 1334]
  rewrite [optimized_3_3]
  rewrite [optimizedChunk_append 3 2000 250 1084]
  rewrite [optimized_3_4]
  rewrite [optimizedChunk_append 3 2250 250 834]
  rewrite [optimized_3_5]
  rewrite [optimizedChunk_append 3 2500 250 584]
  rewrite [optimized_3_6]
  rewrite [optimizedChunk_append 3 2750 250 334]
  rewrite [optimized_3_7]
  rewrite [optimizedChunk_append 3 3000 250 84]
  rewrite [optimized_3_8]
  rewrite [optimized_3_9]
  rfl

private theorem reference_4_0 : referenceChunk 4 1000 250 = [] := by decide +kernel
private theorem reference_4_1 : referenceChunk 4 1250 250 = [] := by decide +kernel
private theorem reference_4_2 : referenceChunk 4 1500 250 = [6952] := by decide +kernel
private theorem reference_4_3 : referenceChunk 4 1750 250 = [7852] := by decide +kernel
private theorem reference_4_4 : referenceChunk 4 2000 250 = [] := by decide +kernel
private theorem reference_4_5 : referenceChunk 4 2250 250 = [] := by decide +kernel

private theorem reference_row4 : referenceChunk 4 (lowerBound 1000 4) (upperBound 9999 4 + 1 - lowerBound 1000 4) = [6952, 7852] := by
  change referenceChunk 4 1000 1500 = _
  rewrite [referenceChunk_append 4 1000 250 1250]
  rewrite [reference_4_0]
  rewrite [referenceChunk_append 4 1250 250 1000]
  rewrite [reference_4_1]
  rewrite [referenceChunk_append 4 1500 250 750]
  rewrite [reference_4_2]
  rewrite [referenceChunk_append 4 1750 250 500]
  rewrite [reference_4_3]
  rewrite [referenceChunk_append 4 2000 250 250]
  rewrite [reference_4_4]
  rewrite [reference_4_5]
  rfl

private theorem optimized_4_0 : optimizedChunk 4 1000 250 = [] := by decide +kernel
private theorem optimized_4_1 : optimizedChunk 4 1250 250 = [] := by decide +kernel
private theorem optimized_4_2 : optimizedChunk 4 1500 250 = [6952] := by decide +kernel
private theorem optimized_4_3 : optimizedChunk 4 1750 250 = [7852] := by decide +kernel
private theorem optimized_4_4 : optimizedChunk 4 2000 250 = [] := by decide +kernel
private theorem optimized_4_5 : optimizedChunk 4 2250 250 = [] := by decide +kernel

private theorem optimized_row4 : row 1000 9999 4 = [6952, 7852] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 4).1 < 0 by decide +kernel)]
  change optimizedChunk 4 1000 1500 = _
  rewrite [optimizedChunk_append 4 1000 250 1250]
  rewrite [optimized_4_0]
  rewrite [optimizedChunk_append 4 1250 250 1000]
  rewrite [optimized_4_1]
  rewrite [optimizedChunk_append 4 1500 250 750]
  rewrite [optimized_4_2]
  rewrite [optimizedChunk_append 4 1750 250 500]
  rewrite [optimized_4_3]
  rewrite [optimizedChunk_append 4 2000 250 250]
  rewrite [optimized_4_4]
  rewrite [optimized_4_5]
  rfl

private theorem reference_5_0 : referenceChunk 5 1000 250 = [] := by decide +kernel
private theorem reference_5_1 : referenceChunk 5 1250 250 = [] := by decide +kernel
private theorem reference_5_2 : referenceChunk 5 1500 250 = [] := by decide +kernel
private theorem reference_5_3 : referenceChunk 5 1750 250 = [] := by decide +kernel

private theorem reference_row5 : referenceChunk 5 (lowerBound 1000 5) (upperBound 9999 5 + 1 - lowerBound 1000 5) = [] := by
  change referenceChunk 5 1000 1000 = _
  rewrite [referenceChunk_append 5 1000 250 750]
  rewrite [reference_5_0]
  rewrite [referenceChunk_append 5 1250 250 500]
  rewrite [reference_5_1]
  rewrite [referenceChunk_append 5 1500 250 250]
  rewrite [reference_5_2]
  rewrite [reference_5_3]
  rfl

private theorem optimized_5_0 : optimizedChunk 5 1000 250 = [] := by decide +kernel
private theorem optimized_5_1 : optimizedChunk 5 1250 250 = [] := by decide +kernel
private theorem optimized_5_2 : optimizedChunk 5 1500 250 = [] := by decide +kernel
private theorem optimized_5_3 : optimizedChunk 5 1750 250 = [] := by decide +kernel

private theorem optimized_row5 : row 1000 9999 5 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 5).1 < 0 by decide +kernel)]
  change optimizedChunk 5 1000 1000 = _
  rewrite [optimizedChunk_append 5 1000 250 750]
  rewrite [optimized_5_0]
  rewrite [optimizedChunk_append 5 1250 250 500]
  rewrite [optimized_5_1]
  rewrite [optimizedChunk_append 5 1500 250 250]
  rewrite [optimized_5_2]
  rewrite [optimized_5_3]
  rfl

private theorem reference_6_0 : referenceChunk 6 1000 250 = [] := by decide +kernel
private theorem reference_6_1 : referenceChunk 6 1250 250 = [] := by decide +kernel
private theorem reference_6_2 : referenceChunk 6 1500 167 = [] := by decide +kernel

private theorem reference_row6 : referenceChunk 6 (lowerBound 1000 6) (upperBound 9999 6 + 1 - lowerBound 1000 6) = [] := by
  change referenceChunk 6 1000 667 = _
  rewrite [referenceChunk_append 6 1000 250 417]
  rewrite [reference_6_0]
  rewrite [referenceChunk_append 6 1250 250 167]
  rewrite [reference_6_1]
  rewrite [reference_6_2]
  rfl

private theorem optimized_6_0 : optimizedChunk 6 1000 250 = [] := by decide +kernel
private theorem optimized_6_1 : optimizedChunk 6 1250 250 = [] := by decide +kernel
private theorem optimized_6_2 : optimizedChunk 6 1500 167 = [] := by decide +kernel

private theorem optimized_row6 : row 1000 9999 6 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 6).1 < 0 by decide +kernel)]
  change optimizedChunk 6 1000 667 = _
  rewrite [optimizedChunk_append 6 1000 250 417]
  rewrite [optimized_6_0]
  rewrite [optimizedChunk_append 6 1250 250 167]
  rewrite [optimized_6_1]
  rewrite [optimized_6_2]
  rfl

private theorem reference_7_0 : referenceChunk 7 1000 250 = [] := by decide +kernel
private theorem reference_7_1 : referenceChunk 7 1250 179 = [] := by decide +kernel

private theorem reference_row7 : referenceChunk 7 (lowerBound 1000 7) (upperBound 9999 7 + 1 - lowerBound 1000 7) = [] := by
  change referenceChunk 7 1000 429 = _
  rewrite [referenceChunk_append 7 1000 250 179]
  rewrite [reference_7_0]
  rewrite [reference_7_1]
  rfl

private theorem optimized_7_0 : optimizedChunk 7 1000 250 = [] := by decide +kernel
private theorem optimized_7_1 : optimizedChunk 7 1250 179 = [] := by decide +kernel

private theorem optimized_row7 : row 1000 9999 7 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 7).1 < 0 by decide +kernel)]
  change optimizedChunk 7 1000 429 = _
  rewrite [optimizedChunk_append 7 1000 250 179]
  rewrite [optimized_7_0]
  rewrite [optimized_7_1]
  rfl

private theorem reference_8_0 : referenceChunk 8 1000 250 = [] := by decide +kernel

private theorem reference_row8 : referenceChunk 8 (lowerBound 1000 8) (upperBound 9999 8 + 1 - lowerBound 1000 8) = [] := by
  change referenceChunk 8 1000 250 = _
  rewrite [reference_8_0]
  rfl

private theorem optimized_8_0 : optimizedChunk 8 1000 250 = [] := by decide +kernel

private theorem optimized_row8 : row 1000 9999 8 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 8).1 < 0 by decide +kernel)]
  change optimizedChunk 8 1000 250 = _
  rewrite [optimized_8_0]
  rfl

private theorem reference_9_0 : referenceChunk 9 1000 112 = [] := by decide +kernel

private theorem reference_row9 : referenceChunk 9 (lowerBound 1000 9) (upperBound 9999 9 + 1 - lowerBound 1000 9) = [] := by
  change referenceChunk 9 1000 112 = _
  rewrite [reference_9_0]
  rfl

private theorem optimized_9_0 : optimizedChunk 9 1000 112 = [] := by decide +kernel

private theorem optimized_row9 : row 1000 9999 9 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 9).1 < 0 by decide +kernel)]
  change optimizedChunk 9 1000 112 = _
  rewrite [optimized_9_0]
  rfl

private theorem reference_10_0 : referenceChunk 10 100 250 = [] := by decide +kernel
private theorem reference_10_1 : referenceChunk 10 350 250 = [] := by decide +kernel
private theorem reference_10_2 : referenceChunk 10 600 250 = [] := by decide +kernel
private theorem reference_10_3 : referenceChunk 10 850 150 = [] := by decide +kernel

private theorem reference_row10 : referenceChunk 10 (lowerBound 100 10) (upperBound 999 10 + 1 - lowerBound 100 10) = [] := by
  change referenceChunk 10 100 900 = _
  rewrite [referenceChunk_append 10 100 250 650]
  rewrite [reference_10_0]
  rewrite [referenceChunk_append 10 350 250 400]
  rewrite [reference_10_1]
  rewrite [referenceChunk_append 10 600 250 150]
  rewrite [reference_10_2]
  rewrite [reference_10_3]
  rfl

private theorem optimized_row10 : row 100 999 10 = [] := by decide +kernel

private theorem reference_11_0 : referenceChunk 11 100 250 = [] := by decide +kernel
private theorem reference_11_1 : referenceChunk 11 350 250 = [] := by decide +kernel
private theorem reference_11_2 : referenceChunk 11 600 250 = [] := by decide +kernel
private theorem reference_11_3 : referenceChunk 11 850 60 = [] := by decide +kernel

private theorem reference_row11 : referenceChunk 11 (lowerBound 100 11) (upperBound 999 11 + 1 - lowerBound 100 11) = [] := by
  change referenceChunk 11 100 810 = _
  rewrite [referenceChunk_append 11 100 250 560]
  rewrite [reference_11_0]
  rewrite [referenceChunk_append 11 350 250 310]
  rewrite [reference_11_1]
  rewrite [referenceChunk_append 11 600 250 60]
  rewrite [reference_11_2]
  rewrite [reference_11_3]
  rfl

private theorem optimized_row11 : row 100 999 11 = [] := by decide +kernel

private theorem reference_12_0 : referenceChunk 12 100 250 = [] := by decide +kernel
private theorem reference_12_1 : referenceChunk 12 350 250 = [5796] := by decide +kernel
private theorem reference_12_2 : referenceChunk 12 600 234 = [] := by decide +kernel

private theorem reference_row12 : referenceChunk 12 (lowerBound 100 12) (upperBound 999 12 + 1 - lowerBound 100 12) = [5796] := by
  change referenceChunk 12 100 734 = _
  rewrite [referenceChunk_append 12 100 250 484]
  rewrite [reference_12_0]
  rewrite [referenceChunk_append 12 350 250 234]
  rewrite [reference_12_1]
  rewrite [reference_12_2]
  rfl

private theorem optimized_12_0 : optimizedChunk 12 100 250 = [] := by decide +kernel
private theorem optimized_12_1 : optimizedChunk 12 350 250 = [5796] := by decide +kernel
private theorem optimized_12_2 : optimizedChunk 12 600 234 = [] := by decide +kernel

private theorem optimized_row12 : row 100 999 12 = [5796] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 12).1 < 0 by decide +kernel)]
  change optimizedChunk 12 100 734 = _
  rewrite [optimizedChunk_append 12 100 250 484]
  rewrite [optimized_12_0]
  rewrite [optimizedChunk_append 12 350 250 234]
  rewrite [optimized_12_1]
  rewrite [optimized_12_2]
  rfl

private theorem reference_13_0 : referenceChunk 13 100 250 = [] := by decide +kernel
private theorem reference_13_1 : referenceChunk 13 350 250 = [] := by decide +kernel
private theorem reference_13_2 : referenceChunk 13 600 170 = [] := by decide +kernel

private theorem reference_row13 : referenceChunk 13 (lowerBound 100 13) (upperBound 999 13 + 1 - lowerBound 100 13) = [] := by
  change referenceChunk 13 100 670 = _
  rewrite [referenceChunk_append 13 100 250 420]
  rewrite [reference_13_0]
  rewrite [referenceChunk_append 13 350 250 170]
  rewrite [reference_13_1]
  rewrite [reference_13_2]
  rfl

private theorem optimized_13_0 : optimizedChunk 13 100 250 = [] := by decide +kernel
private theorem optimized_13_1 : optimizedChunk 13 350 250 = [] := by decide +kernel
private theorem optimized_13_2 : optimizedChunk 13 600 170 = [] := by decide +kernel

private theorem optimized_row13 : row 100 999 13 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 13).1 < 0 by decide +kernel)]
  change optimizedChunk 13 100 670 = _
  rewrite [optimizedChunk_append 13 100 250 420]
  rewrite [optimized_13_0]
  rewrite [optimizedChunk_append 13 350 250 170]
  rewrite [optimized_13_1]
  rewrite [optimized_13_2]
  rfl

private theorem reference_14_0 : referenceChunk 14 100 250 = [] := by decide +kernel
private theorem reference_14_1 : referenceChunk 14 350 250 = [] := by decide +kernel
private theorem reference_14_2 : referenceChunk 14 600 115 = [] := by decide +kernel

private theorem reference_row14 : referenceChunk 14 (lowerBound 100 14) (upperBound 999 14 + 1 - lowerBound 100 14) = [] := by
  change referenceChunk 14 100 615 = _
  rewrite [referenceChunk_append 14 100 250 365]
  rewrite [reference_14_0]
  rewrite [referenceChunk_append 14 350 250 115]
  rewrite [reference_14_1]
  rewrite [reference_14_2]
  rfl

private theorem optimized_14_0 : optimizedChunk 14 100 250 = [] := by decide +kernel
private theorem optimized_14_1 : optimizedChunk 14 350 250 = [] := by decide +kernel
private theorem optimized_14_2 : optimizedChunk 14 600 115 = [] := by decide +kernel

private theorem optimized_row14 : row 100 999 14 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 14).1 < 0 by decide +kernel)]
  change optimizedChunk 14 100 615 = _
  rewrite [optimizedChunk_append 14 100 250 365]
  rewrite [optimized_14_0]
  rewrite [optimizedChunk_append 14 350 250 115]
  rewrite [optimized_14_1]
  rewrite [optimized_14_2]
  rfl

private theorem reference_15_0 : referenceChunk 15 100 250 = [] := by decide +kernel
private theorem reference_15_1 : referenceChunk 15 350 250 = [] := by decide +kernel
private theorem reference_15_2 : referenceChunk 15 600 67 = [] := by decide +kernel

private theorem reference_row15 : referenceChunk 15 (lowerBound 100 15) (upperBound 999 15 + 1 - lowerBound 100 15) = [] := by
  change referenceChunk 15 100 567 = _
  rewrite [referenceChunk_append 15 100 250 317]
  rewrite [reference_15_0]
  rewrite [referenceChunk_append 15 350 250 67]
  rewrite [reference_15_1]
  rewrite [reference_15_2]
  rfl

private theorem optimized_15_0 : optimizedChunk 15 100 250 = [] := by decide +kernel
private theorem optimized_15_1 : optimizedChunk 15 350 250 = [] := by decide +kernel
private theorem optimized_15_2 : optimizedChunk 15 600 67 = [] := by decide +kernel

private theorem optimized_row15 : row 100 999 15 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 15).1 < 0 by decide +kernel)]
  change optimizedChunk 15 100 567 = _
  rewrite [optimizedChunk_append 15 100 250 317]
  rewrite [optimized_15_0]
  rewrite [optimizedChunk_append 15 350 250 67]
  rewrite [optimized_15_1]
  rewrite [optimized_15_2]
  rfl

private theorem reference_16_0 : referenceChunk 16 100 250 = [] := by decide +kernel
private theorem reference_16_1 : referenceChunk 16 350 250 = [] := by decide +kernel
private theorem reference_16_2 : referenceChunk 16 600 25 = [] := by decide +kernel

private theorem reference_row16 : referenceChunk 16 (lowerBound 100 16) (upperBound 999 16 + 1 - lowerBound 100 16) = [] := by
  change referenceChunk 16 100 525 = _
  rewrite [referenceChunk_append 16 100 250 275]
  rewrite [reference_16_0]
  rewrite [referenceChunk_append 16 350 250 25]
  rewrite [reference_16_1]
  rewrite [reference_16_2]
  rfl

private theorem optimized_16_0 : optimizedChunk 16 100 250 = [] := by decide +kernel
private theorem optimized_16_1 : optimizedChunk 16 350 250 = [] := by decide +kernel
private theorem optimized_16_2 : optimizedChunk 16 600 25 = [] := by decide +kernel

private theorem optimized_row16 : row 100 999 16 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 16).1 < 0 by decide +kernel)]
  change optimizedChunk 16 100 525 = _
  rewrite [optimizedChunk_append 16 100 250 275]
  rewrite [optimized_16_0]
  rewrite [optimizedChunk_append 16 350 250 25]
  rewrite [optimized_16_1]
  rewrite [optimized_16_2]
  rfl

private theorem reference_17_0 : referenceChunk 17 100 250 = [] := by decide +kernel
private theorem reference_17_1 : referenceChunk 17 350 239 = [] := by decide +kernel

private theorem reference_row17 : referenceChunk 17 (lowerBound 100 17) (upperBound 999 17 + 1 - lowerBound 100 17) = [] := by
  change referenceChunk 17 100 489 = _
  rewrite [referenceChunk_append 17 100 250 239]
  rewrite [reference_17_0]
  rewrite [reference_17_1]
  rfl

private theorem optimized_17_0 : optimizedChunk 17 100 250 = [] := by decide +kernel
private theorem optimized_17_1 : optimizedChunk 17 350 239 = [] := by decide +kernel

private theorem optimized_row17 : row 100 999 17 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 17).1 < 0 by decide +kernel)]
  change optimizedChunk 17 100 489 = _
  rewrite [optimizedChunk_append 17 100 250 239]
  rewrite [optimized_17_0]
  rewrite [optimized_17_1]
  rfl

private theorem reference_18_0 : referenceChunk 18 100 250 = [5346] := by decide +kernel
private theorem reference_18_1 : referenceChunk 18 350 206 = [] := by decide +kernel

private theorem reference_row18 : referenceChunk 18 (lowerBound 100 18) (upperBound 999 18 + 1 - lowerBound 100 18) = [5346] := by
  change referenceChunk 18 100 456 = _
  rewrite [referenceChunk_append 18 100 250 206]
  rewrite [reference_18_0]
  rewrite [reference_18_1]
  rfl

private theorem optimized_18_0 : optimizedChunk 18 100 250 = [5346] := by decide +kernel
private theorem optimized_18_1 : optimizedChunk 18 350 206 = [] := by decide +kernel

private theorem optimized_row18 : row 100 999 18 = [5346] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 18).1 < 0 by decide +kernel)]
  change optimizedChunk 18 100 456 = _
  rewrite [optimizedChunk_append 18 100 250 206]
  rewrite [optimized_18_0]
  rewrite [optimized_18_1]
  rfl

private theorem reference_19_0 : referenceChunk 19 100 250 = [] := by decide +kernel
private theorem reference_19_1 : referenceChunk 19 350 177 = [] := by decide +kernel

private theorem reference_row19 : referenceChunk 19 (lowerBound 100 19) (upperBound 999 19 + 1 - lowerBound 100 19) = [] := by
  change referenceChunk 19 100 427 = _
  rewrite [referenceChunk_append 19 100 250 177]
  rewrite [reference_19_0]
  rewrite [reference_19_1]
  rfl

private theorem optimized_19_0 : optimizedChunk 19 100 250 = [] := by decide +kernel
private theorem optimized_19_1 : optimizedChunk 19 350 177 = [] := by decide +kernel

private theorem optimized_row19 : row 100 999 19 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 19).1 < 0 by decide +kernel)]
  change optimizedChunk 19 100 427 = _
  rewrite [optimizedChunk_append 19 100 250 177]
  rewrite [optimized_19_0]
  rewrite [optimized_19_1]
  rfl

private theorem reference_20_0 : referenceChunk 20 100 250 = [] := by decide +kernel
private theorem reference_20_1 : referenceChunk 20 350 150 = [] := by decide +kernel

private theorem reference_row20 : referenceChunk 20 (lowerBound 100 20) (upperBound 999 20 + 1 - lowerBound 100 20) = [] := by
  change referenceChunk 20 100 400 = _
  rewrite [referenceChunk_append 20 100 250 150]
  rewrite [reference_20_0]
  rewrite [reference_20_1]
  rfl

private theorem optimized_row20 : row 100 999 20 = [] := by decide +kernel

private theorem reference_21_0 : referenceChunk 21 100 250 = [] := by decide +kernel
private theorem reference_21_1 : referenceChunk 21 350 127 = [] := by decide +kernel

private theorem reference_row21 : referenceChunk 21 (lowerBound 100 21) (upperBound 999 21 + 1 - lowerBound 100 21) = [] := by
  change referenceChunk 21 100 377 = _
  rewrite [referenceChunk_append 21 100 250 127]
  rewrite [reference_21_0]
  rewrite [reference_21_1]
  rfl

private theorem optimized_21_0 : optimizedChunk 21 100 250 = [] := by decide +kernel
private theorem optimized_21_1 : optimizedChunk 21 350 127 = [] := by decide +kernel

private theorem optimized_row21 : row 100 999 21 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 21).1 < 0 by decide +kernel)]
  change optimizedChunk 21 100 377 = _
  rewrite [optimizedChunk_append 21 100 250 127]
  rewrite [optimized_21_0]
  rewrite [optimized_21_1]
  rfl

private theorem reference_22_0 : referenceChunk 22 100 250 = [] := by decide +kernel
private theorem reference_22_1 : referenceChunk 22 350 105 = [] := by decide +kernel

private theorem reference_row22 : referenceChunk 22 (lowerBound 100 22) (upperBound 999 22 + 1 - lowerBound 100 22) = [] := by
  change referenceChunk 22 100 355 = _
  rewrite [referenceChunk_append 22 100 250 105]
  rewrite [reference_22_0]
  rewrite [reference_22_1]
  rfl

private theorem optimized_row22 : row 100 999 22 = [] := by decide +kernel

private theorem reference_23_0 : referenceChunk 23 100 250 = [] := by decide +kernel
private theorem reference_23_1 : referenceChunk 23 350 85 = [] := by decide +kernel

private theorem reference_row23 : referenceChunk 23 (lowerBound 100 23) (upperBound 999 23 + 1 - lowerBound 100 23) = [] := by
  change referenceChunk 23 100 335 = _
  rewrite [referenceChunk_append 23 100 250 85]
  rewrite [reference_23_0]
  rewrite [reference_23_1]
  rfl

private theorem optimized_23_0 : optimizedChunk 23 100 250 = [] := by decide +kernel
private theorem optimized_23_1 : optimizedChunk 23 350 85 = [] := by decide +kernel

private theorem optimized_row23 : row 100 999 23 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 23).1 < 0 by decide +kernel)]
  change optimizedChunk 23 100 335 = _
  rewrite [optimizedChunk_append 23 100 250 85]
  rewrite [optimized_23_0]
  rewrite [optimized_23_1]
  rfl

private theorem reference_24_0 : referenceChunk 24 100 250 = [] := by decide +kernel
private theorem reference_24_1 : referenceChunk 24 350 67 = [] := by decide +kernel

private theorem reference_row24 : referenceChunk 24 (lowerBound 100 24) (upperBound 999 24 + 1 - lowerBound 100 24) = [] := by
  change referenceChunk 24 100 317 = _
  rewrite [referenceChunk_append 24 100 250 67]
  rewrite [reference_24_0]
  rewrite [reference_24_1]
  rfl

private theorem optimized_24_0 : optimizedChunk 24 100 250 = [] := by decide +kernel
private theorem optimized_24_1 : optimizedChunk 24 350 67 = [] := by decide +kernel

private theorem optimized_row24 : row 100 999 24 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 24).1 < 0 by decide +kernel)]
  change optimizedChunk 24 100 317 = _
  rewrite [optimizedChunk_append 24 100 250 67]
  rewrite [optimized_24_0]
  rewrite [optimized_24_1]
  rfl

private theorem reference_25_0 : referenceChunk 25 100 250 = [] := by decide +kernel
private theorem reference_25_1 : referenceChunk 25 350 50 = [] := by decide +kernel

private theorem reference_row25 : referenceChunk 25 (lowerBound 100 25) (upperBound 999 25 + 1 - lowerBound 100 25) = [] := by
  change referenceChunk 25 100 300 = _
  rewrite [referenceChunk_append 25 100 250 50]
  rewrite [reference_25_0]
  rewrite [reference_25_1]
  rfl

private theorem optimized_25_0 : optimizedChunk 25 100 250 = [] := by decide +kernel
private theorem optimized_25_1 : optimizedChunk 25 350 50 = [] := by decide +kernel

private theorem optimized_row25 : row 100 999 25 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 25).1 < 0 by decide +kernel)]
  change optimizedChunk 25 100 300 = _
  rewrite [optimizedChunk_append 25 100 250 50]
  rewrite [optimized_25_0]
  rewrite [optimized_25_1]
  rfl

private theorem reference_26_0 : referenceChunk 26 100 250 = [] := by decide +kernel
private theorem reference_26_1 : referenceChunk 26 350 35 = [] := by decide +kernel

private theorem reference_row26 : referenceChunk 26 (lowerBound 100 26) (upperBound 999 26 + 1 - lowerBound 100 26) = [] := by
  change referenceChunk 26 100 285 = _
  rewrite [referenceChunk_append 26 100 250 35]
  rewrite [reference_26_0]
  rewrite [reference_26_1]
  rfl

private theorem optimized_26_0 : optimizedChunk 26 100 250 = [] := by decide +kernel
private theorem optimized_26_1 : optimizedChunk 26 350 35 = [] := by decide +kernel

private theorem optimized_row26 : row 100 999 26 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 26).1 < 0 by decide +kernel)]
  change optimizedChunk 26 100 285 = _
  rewrite [optimizedChunk_append 26 100 250 35]
  rewrite [optimized_26_0]
  rewrite [optimized_26_1]
  rfl

private theorem reference_27_0 : referenceChunk 27 100 250 = [5346] := by decide +kernel
private theorem reference_27_1 : referenceChunk 27 350 21 = [] := by decide +kernel

private theorem reference_row27 : referenceChunk 27 (lowerBound 100 27) (upperBound 999 27 + 1 - lowerBound 100 27) = [5346] := by
  change referenceChunk 27 100 271 = _
  rewrite [referenceChunk_append 27 100 250 21]
  rewrite [reference_27_0]
  rewrite [reference_27_1]
  rfl

private theorem optimized_27_0 : optimizedChunk 27 100 250 = [5346] := by decide +kernel
private theorem optimized_27_1 : optimizedChunk 27 350 21 = [] := by decide +kernel

private theorem optimized_row27 : row 100 999 27 = [5346] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 27).1 < 0 by decide +kernel)]
  change optimizedChunk 27 100 271 = _
  rewrite [optimizedChunk_append 27 100 250 21]
  rewrite [optimized_27_0]
  rewrite [optimized_27_1]
  rfl

private theorem reference_28_0 : referenceChunk 28 100 250 = [4396] := by decide +kernel
private theorem reference_28_1 : referenceChunk 28 350 8 = [] := by decide +kernel

private theorem reference_row28 : referenceChunk 28 (lowerBound 100 28) (upperBound 999 28 + 1 - lowerBound 100 28) = [4396] := by
  change referenceChunk 28 100 258 = _
  rewrite [referenceChunk_append 28 100 250 8]
  rewrite [reference_28_0]
  rewrite [reference_28_1]
  rfl

private theorem optimized_28_0 : optimizedChunk 28 100 250 = [4396] := by decide +kernel
private theorem optimized_28_1 : optimizedChunk 28 350 8 = [] := by decide +kernel

private theorem optimized_row28 : row 100 999 28 = [4396] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 28).1 < 0 by decide +kernel)]
  change optimizedChunk 28 100 258 = _
  rewrite [optimizedChunk_append 28 100 250 8]
  rewrite [optimized_28_0]
  rewrite [optimized_28_1]
  rfl

private theorem reference_29_0 : referenceChunk 29 100 245 = [] := by decide +kernel

private theorem reference_row29 : referenceChunk 29 (lowerBound 100 29) (upperBound 999 29 + 1 - lowerBound 100 29) = [] := by
  change referenceChunk 29 100 245 = _
  rewrite [reference_29_0]
  rfl

private theorem optimized_29_0 : optimizedChunk 29 100 245 = [] := by decide +kernel

private theorem optimized_row29 : row 100 999 29 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 29).1 < 0 by decide +kernel)]
  change optimizedChunk 29 100 245 = _
  rewrite [optimized_29_0]
  rfl

private theorem reference_30_0 : referenceChunk 30 100 234 = [] := by decide +kernel

private theorem reference_row30 : referenceChunk 30 (lowerBound 100 30) (upperBound 999 30 + 1 - lowerBound 100 30) = [] := by
  change referenceChunk 30 100 234 = _
  rewrite [reference_30_0]
  rfl

private theorem optimized_row30 : row 100 999 30 = [] := by decide +kernel

private theorem reference_31_0 : referenceChunk 31 100 223 = [] := by decide +kernel

private theorem reference_row31 : referenceChunk 31 (lowerBound 100 31) (upperBound 999 31 + 1 - lowerBound 100 31) = [] := by
  change referenceChunk 31 100 223 = _
  rewrite [reference_31_0]
  rfl

private theorem optimized_31_0 : optimizedChunk 31 100 223 = [] := by decide +kernel

private theorem optimized_row31 : row 100 999 31 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 31).1 < 0 by decide +kernel)]
  change optimizedChunk 31 100 223 = _
  rewrite [optimized_31_0]
  rfl

private theorem reference_32_0 : referenceChunk 32 100 213 = [] := by decide +kernel

private theorem reference_row32 : referenceChunk 32 (lowerBound 100 32) (upperBound 999 32 + 1 - lowerBound 100 32) = [] := by
  change referenceChunk 32 100 213 = _
  rewrite [reference_32_0]
  rfl

private theorem optimized_32_0 : optimizedChunk 32 100 213 = [] := by decide +kernel

private theorem optimized_row32 : row 100 999 32 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 32).1 < 0 by decide +kernel)]
  change optimizedChunk 32 100 213 = _
  rewrite [optimized_32_0]
  rfl

private theorem reference_33_0 : referenceChunk 33 100 204 = [] := by decide +kernel

private theorem reference_row33 : referenceChunk 33 (lowerBound 100 33) (upperBound 999 33 + 1 - lowerBound 100 33) = [] := by
  change referenceChunk 33 100 204 = _
  rewrite [reference_33_0]
  rfl

private theorem optimized_row33 : row 100 999 33 = [] := by decide +kernel

private theorem reference_34_0 : referenceChunk 34 100 195 = [] := by decide +kernel

private theorem reference_row34 : referenceChunk 34 (lowerBound 100 34) (upperBound 999 34 + 1 - lowerBound 100 34) = [] := by
  change referenceChunk 34 100 195 = _
  rewrite [reference_34_0]
  rfl

private theorem optimized_34_0 : optimizedChunk 34 100 195 = [] := by decide +kernel

private theorem optimized_row34 : row 100 999 34 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 34).1 < 0 by decide +kernel)]
  change optimizedChunk 34 100 195 = _
  rewrite [optimized_34_0]
  rfl

private theorem reference_35_0 : referenceChunk 35 100 186 = [] := by decide +kernel

private theorem reference_row35 : referenceChunk 35 (lowerBound 100 35) (upperBound 999 35 + 1 - lowerBound 100 35) = [] := by
  change referenceChunk 35 100 186 = _
  rewrite [reference_35_0]
  rfl

private theorem optimized_35_0 : optimizedChunk 35 100 186 = [] := by decide +kernel

private theorem optimized_row35 : row 100 999 35 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 35).1 < 0 by decide +kernel)]
  change optimizedChunk 35 100 186 = _
  rewrite [optimized_35_0]
  rfl

private theorem reference_36_0 : referenceChunk 36 100 178 = [] := by decide +kernel

private theorem reference_row36 : referenceChunk 36 (lowerBound 100 36) (upperBound 999 36 + 1 - lowerBound 100 36) = [] := by
  change referenceChunk 36 100 178 = _
  rewrite [reference_36_0]
  rfl

private theorem optimized_36_0 : optimizedChunk 36 100 178 = [] := by decide +kernel

private theorem optimized_row36 : row 100 999 36 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 36).1 < 0 by decide +kernel)]
  change optimizedChunk 36 100 178 = _
  rewrite [optimized_36_0]
  rfl

private theorem reference_37_0 : referenceChunk 37 100 171 = [] := by decide +kernel

private theorem reference_row37 : referenceChunk 37 (lowerBound 100 37) (upperBound 999 37 + 1 - lowerBound 100 37) = [] := by
  change referenceChunk 37 100 171 = _
  rewrite [reference_37_0]
  rfl

private theorem optimized_37_0 : optimizedChunk 37 100 171 = [] := by decide +kernel

private theorem optimized_row37 : row 100 999 37 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 37).1 < 0 by decide +kernel)]
  change optimizedChunk 37 100 171 = _
  rewrite [optimized_37_0]
  rfl

private theorem reference_38_0 : referenceChunk 38 100 164 = [] := by decide +kernel

private theorem reference_row38 : referenceChunk 38 (lowerBound 100 38) (upperBound 999 38 + 1 - lowerBound 100 38) = [] := by
  change referenceChunk 38 100 164 = _
  rewrite [reference_38_0]
  rfl

private theorem optimized_38_0 : optimizedChunk 38 100 164 = [] := by decide +kernel

private theorem optimized_row38 : row 100 999 38 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 38).1 < 0 by decide +kernel)]
  change optimizedChunk 38 100 164 = _
  rewrite [optimized_38_0]
  rfl

private theorem reference_39_0 : referenceChunk 39 100 157 = [7254] := by decide +kernel

private theorem reference_row39 : referenceChunk 39 (lowerBound 100 39) (upperBound 999 39 + 1 - lowerBound 100 39) = [7254] := by
  change referenceChunk 39 100 157 = _
  rewrite [reference_39_0]
  rfl

private theorem optimized_39_0 : optimizedChunk 39 100 157 = [7254] := by decide +kernel

private theorem optimized_row39 : row 100 999 39 = [7254] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 39).1 < 0 by decide +kernel)]
  change optimizedChunk 39 100 157 = _
  rewrite [optimized_39_0]
  rfl

private theorem reference_40_0 : referenceChunk 40 100 150 = [] := by decide +kernel

private theorem reference_row40 : referenceChunk 40 (lowerBound 100 40) (upperBound 999 40 + 1 - lowerBound 100 40) = [] := by
  change referenceChunk 40 100 150 = _
  rewrite [reference_40_0]
  rfl

private theorem optimized_row40 : row 100 999 40 = [] := by decide +kernel

private theorem reference_41_0 : referenceChunk 41 100 144 = [] := by decide +kernel

private theorem reference_row41 : referenceChunk 41 (lowerBound 100 41) (upperBound 999 41 + 1 - lowerBound 100 41) = [] := by
  change referenceChunk 41 100 144 = _
  rewrite [reference_41_0]
  rfl

private theorem optimized_41_0 : optimizedChunk 41 100 144 = [] := by decide +kernel

private theorem optimized_row41 : row 100 999 41 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 41).1 < 0 by decide +kernel)]
  change optimizedChunk 41 100 144 = _
  rewrite [optimized_41_0]
  rfl

private theorem reference_42_0 : referenceChunk 42 100 139 = [5796] := by decide +kernel

private theorem reference_row42 : referenceChunk 42 (lowerBound 100 42) (upperBound 999 42 + 1 - lowerBound 100 42) = [5796] := by
  change referenceChunk 42 100 139 = _
  rewrite [reference_42_0]
  rfl

private theorem optimized_42_0 : optimizedChunk 42 100 139 = [5796] := by decide +kernel

private theorem optimized_row42 : row 100 999 42 = [5796] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 42).1 < 0 by decide +kernel)]
  change optimizedChunk 42 100 139 = _
  rewrite [optimized_42_0]
  rfl

private theorem reference_43_0 : referenceChunk 43 100 133 = [] := by decide +kernel

private theorem reference_row43 : referenceChunk 43 (lowerBound 100 43) (upperBound 999 43 + 1 - lowerBound 100 43) = [] := by
  change referenceChunk 43 100 133 = _
  rewrite [reference_43_0]
  rfl

private theorem optimized_43_0 : optimizedChunk 43 100 133 = [] := by decide +kernel

private theorem optimized_row43 : row 100 999 43 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 43).1 < 0 by decide +kernel)]
  change optimizedChunk 43 100 133 = _
  rewrite [optimized_43_0]
  rfl

private theorem reference_44_0 : referenceChunk 44 100 128 = [] := by decide +kernel

private theorem reference_row44 : referenceChunk 44 (lowerBound 100 44) (upperBound 999 44 + 1 - lowerBound 100 44) = [] := by
  change referenceChunk 44 100 128 = _
  rewrite [reference_44_0]
  rfl

private theorem optimized_row44 : row 100 999 44 = [] := by decide +kernel

private theorem reference_45_0 : referenceChunk 45 100 123 = [] := by decide +kernel

private theorem reference_row45 : referenceChunk 45 (lowerBound 100 45) (upperBound 999 45 + 1 - lowerBound 100 45) = [] := by
  change referenceChunk 45 100 123 = _
  rewrite [reference_45_0]
  rfl

private theorem optimized_45_0 : optimizedChunk 45 100 123 = [] := by decide +kernel

private theorem optimized_row45 : row 100 999 45 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 45).1 < 0 by decide +kernel)]
  change optimizedChunk 45 100 123 = _
  rewrite [optimized_45_0]
  rfl

private theorem reference_46_0 : referenceChunk 46 100 118 = [] := by decide +kernel

private theorem reference_row46 : referenceChunk 46 (lowerBound 100 46) (upperBound 999 46 + 1 - lowerBound 100 46) = [] := by
  change referenceChunk 46 100 118 = _
  rewrite [reference_46_0]
  rfl

private theorem optimized_46_0 : optimizedChunk 46 100 118 = [] := by decide +kernel

private theorem optimized_row46 : row 100 999 46 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 46).1 < 0 by decide +kernel)]
  change optimizedChunk 46 100 118 = _
  rewrite [optimized_46_0]
  rfl

private theorem reference_47_0 : referenceChunk 47 100 113 = [] := by decide +kernel

private theorem reference_row47 : referenceChunk 47 (lowerBound 100 47) (upperBound 999 47 + 1 - lowerBound 100 47) = [] := by
  change referenceChunk 47 100 113 = _
  rewrite [reference_47_0]
  rfl

private theorem optimized_47_0 : optimizedChunk 47 100 113 = [] := by decide +kernel

private theorem optimized_row47 : row 100 999 47 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 47).1 < 0 by decide +kernel)]
  change optimizedChunk 47 100 113 = _
  rewrite [optimized_47_0]
  rfl

private theorem reference_48_0 : referenceChunk 48 100 109 = [7632] := by decide +kernel

private theorem reference_row48 : referenceChunk 48 (lowerBound 100 48) (upperBound 999 48 + 1 - lowerBound 100 48) = [7632] := by
  change referenceChunk 48 100 109 = _
  rewrite [reference_48_0]
  rfl

private theorem optimized_48_0 : optimizedChunk 48 100 109 = [7632] := by decide +kernel

private theorem optimized_row48 : row 100 999 48 = [7632] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 48).1 < 0 by decide +kernel)]
  change optimizedChunk 48 100 109 = _
  rewrite [optimized_48_0]
  rfl

private theorem reference_49_0 : referenceChunk 49 100 105 = [] := by decide +kernel

private theorem reference_row49 : referenceChunk 49 (lowerBound 100 49) (upperBound 999 49 + 1 - lowerBound 100 49) = [] := by
  change referenceChunk 49 100 105 = _
  rewrite [reference_49_0]
  rfl

private theorem optimized_49_0 : optimizedChunk 49 100 105 = [] := by decide +kernel

private theorem optimized_row49 : row 100 999 49 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 49).1 < 0 by decide +kernel)]
  change optimizedChunk 49 100 105 = _
  rewrite [optimized_49_0]
  rfl

private theorem reference_50_0 : referenceChunk 50 100 100 = [] := by decide +kernel

private theorem reference_row50 : referenceChunk 50 (lowerBound 100 50) (upperBound 999 50 + 1 - lowerBound 100 50) = [] := by
  change referenceChunk 50 100 100 = _
  rewrite [reference_50_0]
  rfl

private theorem optimized_row50 : row 100 999 50 = [] := by decide +kernel

private theorem reference_51_0 : referenceChunk 51 100 97 = [] := by decide +kernel

private theorem reference_row51 : referenceChunk 51 (lowerBound 100 51) (upperBound 999 51 + 1 - lowerBound 100 51) = [] := by
  change referenceChunk 51 100 97 = _
  rewrite [reference_51_0]
  rfl

private theorem optimized_51_0 : optimizedChunk 51 100 97 = [] := by decide +kernel

private theorem optimized_row51 : row 100 999 51 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 51).1 < 0 by decide +kernel)]
  change optimizedChunk 51 100 97 = _
  rewrite [optimized_51_0]
  rfl

private theorem reference_52_0 : referenceChunk 52 100 93 = [] := by decide +kernel

private theorem reference_row52 : referenceChunk 52 (lowerBound 100 52) (upperBound 999 52 + 1 - lowerBound 100 52) = [] := by
  change referenceChunk 52 100 93 = _
  rewrite [reference_52_0]
  rfl

private theorem optimized_52_0 : optimizedChunk 52 100 93 = [] := by decide +kernel

private theorem optimized_row52 : row 100 999 52 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 52).1 < 0 by decide +kernel)]
  change optimizedChunk 52 100 93 = _
  rewrite [optimized_52_0]
  rfl

private theorem reference_53_0 : referenceChunk 53 100 89 = [] := by decide +kernel

private theorem reference_row53 : referenceChunk 53 (lowerBound 100 53) (upperBound 999 53 + 1 - lowerBound 100 53) = [] := by
  change referenceChunk 53 100 89 = _
  rewrite [reference_53_0]
  rfl

private theorem optimized_53_0 : optimizedChunk 53 100 89 = [] := by decide +kernel

private theorem optimized_row53 : row 100 999 53 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 53).1 < 0 by decide +kernel)]
  change optimizedChunk 53 100 89 = _
  rewrite [optimized_53_0]
  rfl

private theorem reference_54_0 : referenceChunk 54 100 86 = [] := by decide +kernel

private theorem reference_row54 : referenceChunk 54 (lowerBound 100 54) (upperBound 999 54 + 1 - lowerBound 100 54) = [] := by
  change referenceChunk 54 100 86 = _
  rewrite [reference_54_0]
  rfl

private theorem optimized_54_0 : optimizedChunk 54 100 86 = [] := by decide +kernel

private theorem optimized_row54 : row 100 999 54 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 54).1 < 0 by decide +kernel)]
  change optimizedChunk 54 100 86 = _
  rewrite [optimized_54_0]
  rfl

private theorem reference_55_0 : referenceChunk 55 100 82 = [] := by decide +kernel

private theorem reference_row55 : referenceChunk 55 (lowerBound 100 55) (upperBound 999 55 + 1 - lowerBound 100 55) = [] := by
  change referenceChunk 55 100 82 = _
  rewrite [reference_55_0]
  rfl

private theorem optimized_row55 : row 100 999 55 = [] := by decide +kernel

private theorem reference_56_0 : referenceChunk 56 100 79 = [] := by decide +kernel

private theorem reference_row56 : referenceChunk 56 (lowerBound 100 56) (upperBound 999 56 + 1 - lowerBound 100 56) = [] := by
  change referenceChunk 56 100 79 = _
  rewrite [reference_56_0]
  rfl

private theorem optimized_56_0 : optimizedChunk 56 100 79 = [] := by decide +kernel

private theorem optimized_row56 : row 100 999 56 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 56).1 < 0 by decide +kernel)]
  change optimizedChunk 56 100 79 = _
  rewrite [optimized_56_0]
  rfl

private theorem reference_57_0 : referenceChunk 57 100 76 = [] := by decide +kernel

private theorem reference_row57 : referenceChunk 57 (lowerBound 100 57) (upperBound 999 57 + 1 - lowerBound 100 57) = [] := by
  change referenceChunk 57 100 76 = _
  rewrite [reference_57_0]
  rfl

private theorem optimized_57_0 : optimizedChunk 57 100 76 = [] := by decide +kernel

private theorem optimized_row57 : row 100 999 57 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 57).1 < 0 by decide +kernel)]
  change optimizedChunk 57 100 76 = _
  rewrite [optimized_57_0]
  rfl

private theorem reference_58_0 : referenceChunk 58 100 73 = [] := by decide +kernel

private theorem reference_row58 : referenceChunk 58 (lowerBound 100 58) (upperBound 999 58 + 1 - lowerBound 100 58) = [] := by
  change referenceChunk 58 100 73 = _
  rewrite [reference_58_0]
  rfl

private theorem optimized_58_0 : optimizedChunk 58 100 73 = [] := by decide +kernel

private theorem optimized_row58 : row 100 999 58 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 58).1 < 0 by decide +kernel)]
  change optimizedChunk 58 100 73 = _
  rewrite [optimized_58_0]
  rfl

private theorem reference_59_0 : referenceChunk 59 100 70 = [] := by decide +kernel

private theorem reference_row59 : referenceChunk 59 (lowerBound 100 59) (upperBound 999 59 + 1 - lowerBound 100 59) = [] := by
  change referenceChunk 59 100 70 = _
  rewrite [reference_59_0]
  rfl

private theorem optimized_59_0 : optimizedChunk 59 100 70 = [] := by decide +kernel

private theorem optimized_row59 : row 100 999 59 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 59).1 < 0 by decide +kernel)]
  change optimizedChunk 59 100 70 = _
  rewrite [optimized_59_0]
  rfl

private theorem reference_60_0 : referenceChunk 60 100 67 = [] := by decide +kernel

private theorem reference_row60 : referenceChunk 60 (lowerBound 100 60) (upperBound 999 60 + 1 - lowerBound 100 60) = [] := by
  change referenceChunk 60 100 67 = _
  rewrite [reference_60_0]
  rfl

private theorem optimized_row60 : row 100 999 60 = [] := by decide +kernel

private theorem reference_61_0 : referenceChunk 61 100 64 = [] := by decide +kernel

private theorem reference_row61 : referenceChunk 61 (lowerBound 100 61) (upperBound 999 61 + 1 - lowerBound 100 61) = [] := by
  change referenceChunk 61 100 64 = _
  rewrite [reference_61_0]
  rfl

private theorem optimized_61_0 : optimizedChunk 61 100 64 = [] := by decide +kernel

private theorem optimized_row61 : row 100 999 61 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 61).1 < 0 by decide +kernel)]
  change optimizedChunk 61 100 64 = _
  rewrite [optimized_61_0]
  rfl

private theorem reference_62_0 : referenceChunk 62 100 62 = [] := by decide +kernel

private theorem reference_row62 : referenceChunk 62 (lowerBound 100 62) (upperBound 999 62 + 1 - lowerBound 100 62) = [] := by
  change referenceChunk 62 100 62 = _
  rewrite [reference_62_0]
  rfl

private theorem optimized_62_0 : optimizedChunk 62 100 62 = [] := by decide +kernel

private theorem optimized_row62 : row 100 999 62 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 62).1 < 0 by decide +kernel)]
  change optimizedChunk 62 100 62 = _
  rewrite [optimized_62_0]
  rfl

private theorem reference_63_0 : referenceChunk 63 100 59 = [] := by decide +kernel

private theorem reference_row63 : referenceChunk 63 (lowerBound 100 63) (upperBound 999 63 + 1 - lowerBound 100 63) = [] := by
  change referenceChunk 63 100 59 = _
  rewrite [reference_63_0]
  rfl

private theorem optimized_63_0 : optimizedChunk 63 100 59 = [] := by decide +kernel

private theorem optimized_row63 : row 100 999 63 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 63).1 < 0 by decide +kernel)]
  change optimizedChunk 63 100 59 = _
  rewrite [optimized_63_0]
  rfl

private theorem reference_64_0 : referenceChunk 64 100 57 = [] := by decide +kernel

private theorem reference_row64 : referenceChunk 64 (lowerBound 100 64) (upperBound 999 64 + 1 - lowerBound 100 64) = [] := by
  change referenceChunk 64 100 57 = _
  rewrite [reference_64_0]
  rfl

private theorem optimized_64_0 : optimizedChunk 64 100 57 = [] := by decide +kernel

private theorem optimized_row64 : row 100 999 64 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 64).1 < 0 by decide +kernel)]
  change optimizedChunk 64 100 57 = _
  rewrite [optimized_64_0]
  rfl

private theorem reference_65_0 : referenceChunk 65 100 54 = [] := by decide +kernel

private theorem reference_row65 : referenceChunk 65 (lowerBound 100 65) (upperBound 999 65 + 1 - lowerBound 100 65) = [] := by
  change referenceChunk 65 100 54 = _
  rewrite [reference_65_0]
  rfl

private theorem optimized_65_0 : optimizedChunk 65 100 54 = [] := by decide +kernel

private theorem optimized_row65 : row 100 999 65 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 65).1 < 0 by decide +kernel)]
  change optimizedChunk 65 100 54 = _
  rewrite [optimized_65_0]
  rfl

private theorem reference_66_0 : referenceChunk 66 100 52 = [] := by decide +kernel

private theorem reference_row66 : referenceChunk 66 (lowerBound 100 66) (upperBound 999 66 + 1 - lowerBound 100 66) = [] := by
  change referenceChunk 66 100 52 = _
  rewrite [reference_66_0]
  rfl

private theorem optimized_row66 : row 100 999 66 = [] := by decide +kernel

private theorem reference_67_0 : referenceChunk 67 100 50 = [] := by decide +kernel

private theorem reference_row67 : referenceChunk 67 (lowerBound 100 67) (upperBound 999 67 + 1 - lowerBound 100 67) = [] := by
  change referenceChunk 67 100 50 = _
  rewrite [reference_67_0]
  rfl

private theorem optimized_67_0 : optimizedChunk 67 100 50 = [] := by decide +kernel

private theorem optimized_row67 : row 100 999 67 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 67).1 < 0 by decide +kernel)]
  change optimizedChunk 67 100 50 = _
  rewrite [optimized_67_0]
  rfl

private theorem reference_68_0 : referenceChunk 68 100 48 = [] := by decide +kernel

private theorem reference_row68 : referenceChunk 68 (lowerBound 100 68) (upperBound 999 68 + 1 - lowerBound 100 68) = [] := by
  change referenceChunk 68 100 48 = _
  rewrite [reference_68_0]
  rfl

private theorem optimized_68_0 : optimizedChunk 68 100 48 = [] := by decide +kernel

private theorem optimized_row68 : row 100 999 68 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 68).1 < 0 by decide +kernel)]
  change optimizedChunk 68 100 48 = _
  rewrite [optimized_68_0]
  rfl

private theorem reference_69_0 : referenceChunk 69 100 45 = [] := by decide +kernel

private theorem reference_row69 : referenceChunk 69 (lowerBound 100 69) (upperBound 999 69 + 1 - lowerBound 100 69) = [] := by
  change referenceChunk 69 100 45 = _
  rewrite [reference_69_0]
  rfl

private theorem optimized_69_0 : optimizedChunk 69 100 45 = [] := by decide +kernel

private theorem optimized_row69 : row 100 999 69 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 69).1 < 0 by decide +kernel)]
  change optimizedChunk 69 100 45 = _
  rewrite [optimized_69_0]
  rfl

private theorem reference_70_0 : referenceChunk 70 100 43 = [] := by decide +kernel

private theorem reference_row70 : referenceChunk 70 (lowerBound 100 70) (upperBound 999 70 + 1 - lowerBound 100 70) = [] := by
  change referenceChunk 70 100 43 = _
  rewrite [reference_70_0]
  rfl

private theorem optimized_row70 : row 100 999 70 = [] := by decide +kernel

private theorem reference_71_0 : referenceChunk 71 100 41 = [] := by decide +kernel

private theorem reference_row71 : referenceChunk 71 (lowerBound 100 71) (upperBound 999 71 + 1 - lowerBound 100 71) = [] := by
  change referenceChunk 71 100 41 = _
  rewrite [reference_71_0]
  rfl

private theorem optimized_71_0 : optimizedChunk 71 100 41 = [] := by decide +kernel

private theorem optimized_row71 : row 100 999 71 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 71).1 < 0 by decide +kernel)]
  change optimizedChunk 71 100 41 = _
  rewrite [optimized_71_0]
  rfl

private theorem reference_72_0 : referenceChunk 72 100 39 = [] := by decide +kernel

private theorem reference_row72 : referenceChunk 72 (lowerBound 100 72) (upperBound 999 72 + 1 - lowerBound 100 72) = [] := by
  change referenceChunk 72 100 39 = _
  rewrite [reference_72_0]
  rfl

private theorem optimized_72_0 : optimizedChunk 72 100 39 = [] := by decide +kernel

private theorem optimized_row72 : row 100 999 72 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 72).1 < 0 by decide +kernel)]
  change optimizedChunk 72 100 39 = _
  rewrite [optimized_72_0]
  rfl

private theorem reference_73_0 : referenceChunk 73 100 37 = [] := by decide +kernel

private theorem reference_row73 : referenceChunk 73 (lowerBound 100 73) (upperBound 999 73 + 1 - lowerBound 100 73) = [] := by
  change referenceChunk 73 100 37 = _
  rewrite [reference_73_0]
  rfl

private theorem optimized_73_0 : optimizedChunk 73 100 37 = [] := by decide +kernel

private theorem optimized_row73 : row 100 999 73 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 73).1 < 0 by decide +kernel)]
  change optimizedChunk 73 100 37 = _
  rewrite [optimized_73_0]
  rfl

private theorem reference_74_0 : referenceChunk 74 100 36 = [] := by decide +kernel

private theorem reference_row74 : referenceChunk 74 (lowerBound 100 74) (upperBound 999 74 + 1 - lowerBound 100 74) = [] := by
  change referenceChunk 74 100 36 = _
  rewrite [reference_74_0]
  rfl

private theorem optimized_74_0 : optimizedChunk 74 100 36 = [] := by decide +kernel

private theorem optimized_row74 : row 100 999 74 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 74).1 < 0 by decide +kernel)]
  change optimizedChunk 74 100 36 = _
  rewrite [optimized_74_0]
  rfl

private theorem reference_75_0 : referenceChunk 75 100 34 = [] := by decide +kernel

private theorem reference_row75 : referenceChunk 75 (lowerBound 100 75) (upperBound 999 75 + 1 - lowerBound 100 75) = [] := by
  change referenceChunk 75 100 34 = _
  rewrite [reference_75_0]
  rfl

private theorem optimized_75_0 : optimizedChunk 75 100 34 = [] := by decide +kernel

private theorem optimized_row75 : row 100 999 75 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 75).1 < 0 by decide +kernel)]
  change optimizedChunk 75 100 34 = _
  rewrite [optimized_75_0]
  rfl

private theorem reference_76_0 : referenceChunk 76 100 32 = [] := by decide +kernel

private theorem reference_row76 : referenceChunk 76 (lowerBound 100 76) (upperBound 999 76 + 1 - lowerBound 100 76) = [] := by
  change referenceChunk 76 100 32 = _
  rewrite [reference_76_0]
  rfl

private theorem optimized_76_0 : optimizedChunk 76 100 32 = [] := by decide +kernel

private theorem optimized_row76 : row 100 999 76 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 76).1 < 0 by decide +kernel)]
  change optimizedChunk 76 100 32 = _
  rewrite [optimized_76_0]
  rfl

private theorem reference_77_0 : referenceChunk 77 100 30 = [] := by decide +kernel

private theorem reference_row77 : referenceChunk 77 (lowerBound 100 77) (upperBound 999 77 + 1 - lowerBound 100 77) = [] := by
  change referenceChunk 77 100 30 = _
  rewrite [reference_77_0]
  rfl

private theorem optimized_row77 : row 100 999 77 = [] := by decide +kernel

private theorem reference_78_0 : referenceChunk 78 100 29 = [] := by decide +kernel

private theorem reference_row78 : referenceChunk 78 (lowerBound 100 78) (upperBound 999 78 + 1 - lowerBound 100 78) = [] := by
  change referenceChunk 78 100 29 = _
  rewrite [reference_78_0]
  rfl

private theorem optimized_78_0 : optimizedChunk 78 100 29 = [] := by decide +kernel

private theorem optimized_row78 : row 100 999 78 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 78).1 < 0 by decide +kernel)]
  change optimizedChunk 78 100 29 = _
  rewrite [optimized_78_0]
  rfl

private theorem reference_79_0 : referenceChunk 79 100 27 = [] := by decide +kernel

private theorem reference_row79 : referenceChunk 79 (lowerBound 100 79) (upperBound 999 79 + 1 - lowerBound 100 79) = [] := by
  change referenceChunk 79 100 27 = _
  rewrite [reference_79_0]
  rfl

private theorem optimized_79_0 : optimizedChunk 79 100 27 = [] := by decide +kernel

private theorem optimized_row79 : row 100 999 79 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 79).1 < 0 by decide +kernel)]
  change optimizedChunk 79 100 27 = _
  rewrite [optimized_79_0]
  rfl

private theorem reference_80_0 : referenceChunk 80 100 25 = [] := by decide +kernel

private theorem reference_row80 : referenceChunk 80 (lowerBound 100 80) (upperBound 999 80 + 1 - lowerBound 100 80) = [] := by
  change referenceChunk 80 100 25 = _
  rewrite [reference_80_0]
  rfl

private theorem optimized_row80 : row 100 999 80 = [] := by decide +kernel

private theorem reference_81_0 : referenceChunk 81 100 24 = [] := by decide +kernel

private theorem reference_row81 : referenceChunk 81 (lowerBound 100 81) (upperBound 999 81 + 1 - lowerBound 100 81) = [] := by
  change referenceChunk 81 100 24 = _
  rewrite [reference_81_0]
  rfl

private theorem optimized_81_0 : optimizedChunk 81 100 24 = [] := by decide +kernel

private theorem optimized_row81 : row 100 999 81 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 81).1 < 0 by decide +kernel)]
  change optimizedChunk 81 100 24 = _
  rewrite [optimized_81_0]
  rfl

private theorem reference_82_0 : referenceChunk 82 100 22 = [] := by decide +kernel

private theorem reference_row82 : referenceChunk 82 (lowerBound 100 82) (upperBound 999 82 + 1 - lowerBound 100 82) = [] := by
  change referenceChunk 82 100 22 = _
  rewrite [reference_82_0]
  rfl

private theorem optimized_82_0 : optimizedChunk 82 100 22 = [] := by decide +kernel

private theorem optimized_row82 : row 100 999 82 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 82).1 < 0 by decide +kernel)]
  change optimizedChunk 82 100 22 = _
  rewrite [optimized_82_0]
  rfl

private theorem reference_83_0 : referenceChunk 83 100 21 = [] := by decide +kernel

private theorem reference_row83 : referenceChunk 83 (lowerBound 100 83) (upperBound 999 83 + 1 - lowerBound 100 83) = [] := by
  change referenceChunk 83 100 21 = _
  rewrite [reference_83_0]
  rfl

private theorem optimized_83_0 : optimizedChunk 83 100 21 = [] := by decide +kernel

private theorem optimized_row83 : row 100 999 83 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 83).1 < 0 by decide +kernel)]
  change optimizedChunk 83 100 21 = _
  rewrite [optimized_83_0]
  rfl

private theorem reference_84_0 : referenceChunk 84 100 20 = [] := by decide +kernel

private theorem reference_row84 : referenceChunk 84 (lowerBound 100 84) (upperBound 999 84 + 1 - lowerBound 100 84) = [] := by
  change referenceChunk 84 100 20 = _
  rewrite [reference_84_0]
  rfl

private theorem optimized_84_0 : optimizedChunk 84 100 20 = [] := by decide +kernel

private theorem optimized_row84 : row 100 999 84 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 84).1 < 0 by decide +kernel)]
  change optimizedChunk 84 100 20 = _
  rewrite [optimized_84_0]
  rfl

private theorem reference_85_0 : referenceChunk 85 100 18 = [] := by decide +kernel

private theorem reference_row85 : referenceChunk 85 (lowerBound 100 85) (upperBound 999 85 + 1 - lowerBound 100 85) = [] := by
  change referenceChunk 85 100 18 = _
  rewrite [reference_85_0]
  rfl

private theorem optimized_85_0 : optimizedChunk 85 100 18 = [] := by decide +kernel

private theorem optimized_row85 : row 100 999 85 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 85).1 < 0 by decide +kernel)]
  change optimizedChunk 85 100 18 = _
  rewrite [optimized_85_0]
  rfl

private theorem reference_86_0 : referenceChunk 86 100 17 = [] := by decide +kernel

private theorem reference_row86 : referenceChunk 86 (lowerBound 100 86) (upperBound 999 86 + 1 - lowerBound 100 86) = [] := by
  change referenceChunk 86 100 17 = _
  rewrite [reference_86_0]
  rfl

private theorem optimized_86_0 : optimizedChunk 86 100 17 = [] := by decide +kernel

private theorem optimized_row86 : row 100 999 86 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 86).1 < 0 by decide +kernel)]
  change optimizedChunk 86 100 17 = _
  rewrite [optimized_86_0]
  rfl

private theorem reference_87_0 : referenceChunk 87 100 15 = [] := by decide +kernel

private theorem reference_row87 : referenceChunk 87 (lowerBound 100 87) (upperBound 999 87 + 1 - lowerBound 100 87) = [] := by
  change referenceChunk 87 100 15 = _
  rewrite [reference_87_0]
  rfl

private theorem optimized_87_0 : optimizedChunk 87 100 15 = [] := by decide +kernel

private theorem optimized_row87 : row 100 999 87 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 87).1 < 0 by decide +kernel)]
  change optimizedChunk 87 100 15 = _
  rewrite [optimized_87_0]
  rfl

private theorem reference_88_0 : referenceChunk 88 100 14 = [] := by decide +kernel

private theorem reference_row88 : referenceChunk 88 (lowerBound 100 88) (upperBound 999 88 + 1 - lowerBound 100 88) = [] := by
  change referenceChunk 88 100 14 = _
  rewrite [reference_88_0]
  rfl

private theorem optimized_row88 : row 100 999 88 = [] := by decide +kernel

private theorem reference_89_0 : referenceChunk 89 100 13 = [] := by decide +kernel

private theorem reference_row89 : referenceChunk 89 (lowerBound 100 89) (upperBound 999 89 + 1 - lowerBound 100 89) = [] := by
  change referenceChunk 89 100 13 = _
  rewrite [reference_89_0]
  rfl

private theorem optimized_89_0 : optimizedChunk 89 100 13 = [] := by decide +kernel

private theorem optimized_row89 : row 100 999 89 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 89).1 < 0 by decide +kernel)]
  change optimizedChunk 89 100 13 = _
  rewrite [optimized_89_0]
  rfl

private theorem reference_90_0 : referenceChunk 90 100 12 = [] := by decide +kernel

private theorem reference_row90 : referenceChunk 90 (lowerBound 100 90) (upperBound 999 90 + 1 - lowerBound 100 90) = [] := by
  change referenceChunk 90 100 12 = _
  rewrite [reference_90_0]
  rfl

private theorem optimized_row90 : row 100 999 90 = [] := by decide +kernel

private theorem reference_91_0 : referenceChunk 91 100 10 = [] := by decide +kernel

private theorem reference_row91 : referenceChunk 91 (lowerBound 100 91) (upperBound 999 91 + 1 - lowerBound 100 91) = [] := by
  change referenceChunk 91 100 10 = _
  rewrite [reference_91_0]
  rfl

private theorem optimized_91_0 : optimizedChunk 91 100 10 = [] := by decide +kernel

private theorem optimized_row91 : row 100 999 91 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 91).1 < 0 by decide +kernel)]
  change optimizedChunk 91 100 10 = _
  rewrite [optimized_91_0]
  rfl

private theorem reference_92_0 : referenceChunk 92 100 9 = [] := by decide +kernel

private theorem reference_row92 : referenceChunk 92 (lowerBound 100 92) (upperBound 999 92 + 1 - lowerBound 100 92) = [] := by
  change referenceChunk 92 100 9 = _
  rewrite [reference_92_0]
  rfl

private theorem optimized_92_0 : optimizedChunk 92 100 9 = [] := by decide +kernel

private theorem optimized_row92 : row 100 999 92 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 92).1 < 0 by decide +kernel)]
  change optimizedChunk 92 100 9 = _
  rewrite [optimized_92_0]
  rfl

private theorem reference_93_0 : referenceChunk 93 100 8 = [] := by decide +kernel

private theorem reference_row93 : referenceChunk 93 (lowerBound 100 93) (upperBound 999 93 + 1 - lowerBound 100 93) = [] := by
  change referenceChunk 93 100 8 = _
  rewrite [reference_93_0]
  rfl

private theorem optimized_93_0 : optimizedChunk 93 100 8 = [] := by decide +kernel

private theorem optimized_row93 : row 100 999 93 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 93).1 < 0 by decide +kernel)]
  change optimizedChunk 93 100 8 = _
  rewrite [optimized_93_0]
  rfl

private theorem reference_94_0 : referenceChunk 94 100 7 = [] := by decide +kernel

private theorem reference_row94 : referenceChunk 94 (lowerBound 100 94) (upperBound 999 94 + 1 - lowerBound 100 94) = [] := by
  change referenceChunk 94 100 7 = _
  rewrite [reference_94_0]
  rfl

private theorem optimized_94_0 : optimizedChunk 94 100 7 = [] := by decide +kernel

private theorem optimized_row94 : row 100 999 94 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 94).1 < 0 by decide +kernel)]
  change optimizedChunk 94 100 7 = _
  rewrite [optimized_94_0]
  rfl

private theorem reference_95_0 : referenceChunk 95 100 6 = [] := by decide +kernel

private theorem reference_row95 : referenceChunk 95 (lowerBound 100 95) (upperBound 999 95 + 1 - lowerBound 100 95) = [] := by
  change referenceChunk 95 100 6 = _
  rewrite [reference_95_0]
  rfl

private theorem optimized_95_0 : optimizedChunk 95 100 6 = [] := by decide +kernel

private theorem optimized_row95 : row 100 999 95 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 95).1 < 0 by decide +kernel)]
  change optimizedChunk 95 100 6 = _
  rewrite [optimized_95_0]
  rfl

private theorem reference_96_0 : referenceChunk 96 100 5 = [] := by decide +kernel

private theorem reference_row96 : referenceChunk 96 (lowerBound 100 96) (upperBound 999 96 + 1 - lowerBound 100 96) = [] := by
  change referenceChunk 96 100 5 = _
  rewrite [reference_96_0]
  rfl

private theorem optimized_96_0 : optimizedChunk 96 100 5 = [] := by decide +kernel

private theorem optimized_row96 : row 100 999 96 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 96).1 < 0 by decide +kernel)]
  change optimizedChunk 96 100 5 = _
  rewrite [optimized_96_0]
  rfl

private theorem reference_97_0 : referenceChunk 97 100 4 = [] := by decide +kernel

private theorem reference_row97 : referenceChunk 97 (lowerBound 100 97) (upperBound 999 97 + 1 - lowerBound 100 97) = [] := by
  change referenceChunk 97 100 4 = _
  rewrite [reference_97_0]
  rfl

private theorem optimized_97_0 : optimizedChunk 97 100 4 = [] := by decide +kernel

private theorem optimized_row97 : row 100 999 97 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 97).1 < 0 by decide +kernel)]
  change optimizedChunk 97 100 4 = _
  rewrite [optimized_97_0]
  rfl

private theorem reference_98_0 : referenceChunk 98 100 3 = [] := by decide +kernel

private theorem reference_row98 : referenceChunk 98 (lowerBound 100 98) (upperBound 999 98 + 1 - lowerBound 100 98) = [] := by
  change referenceChunk 98 100 3 = _
  rewrite [reference_98_0]
  rfl

private theorem optimized_98_0 : optimizedChunk 98 100 3 = [] := by decide +kernel

private theorem optimized_row98 : row 100 999 98 = [] := by
  unfold row
  rewrite [if_neg (show ¬ (digitMask 98).1 < 0 by decide +kernel)]
  change optimizedChunk 98 100 3 = _
  rewrite [optimized_98_0]
  rfl

private theorem reference_99_0 : referenceChunk 99 100 2 = [] := by decide +kernel

private theorem reference_row99 : referenceChunk 99 (lowerBound 100 99) (upperBound 999 99 + 1 - lowerBound 100 99) = [] := by
  change referenceChunk 99 100 2 = _
  rewrite [reference_99_0]
  rfl

private theorem optimized_row99 : row 100 999 99 = [] := by decide +kernel

def productsFound : List Nat := [6952, 7852, 5796, 5346, 5346, 4396, 7254, 5796, 7632]

theorem reference_products :
    (List.range' 1 9).flatMap (fun a => referenceChunk a (lowerBound 1000 a)
      (upperBound 9999 a + 1 - lowerBound 1000 a)) ++
    (List.range' 10 90).flatMap (fun a => referenceChunk a (lowerBound 100 a)
      (upperBound 999 a + 1 - lowerBound 100 a)) = productsFound := by
  change (referenceChunk 1 (lowerBound 1000 1) (upperBound 9999 1 + 1 - lowerBound 1000 1) ++ (referenceChunk 2 (lowerBound 1000 2) (upperBound 9999 2 + 1 - lowerBound 1000 2) ++ (referenceChunk 3 (lowerBound 1000 3) (upperBound 9999 3 + 1 - lowerBound 1000 3) ++ (referenceChunk 4 (lowerBound 1000 4) (upperBound 9999 4 + 1 - lowerBound 1000 4) ++ (referenceChunk 5 (lowerBound 1000 5) (upperBound 9999 5 + 1 - lowerBound 1000 5) ++ (referenceChunk 6 (lowerBound 1000 6) (upperBound 9999 6 + 1 - lowerBound 1000 6) ++ (referenceChunk 7 (lowerBound 1000 7) (upperBound 9999 7 + 1 - lowerBound 1000 7) ++ (referenceChunk 8 (lowerBound 1000 8) (upperBound 9999 8 + 1 - lowerBound 1000 8) ++ (referenceChunk 9 (lowerBound 1000 9) (upperBound 9999 9 + 1 - lowerBound 1000 9) ++ []))))))))) ++ (referenceChunk 10 (lowerBound 100 10) (upperBound 999 10 + 1 - lowerBound 100 10) ++ (referenceChunk 11 (lowerBound 100 11) (upperBound 999 11 + 1 - lowerBound 100 11) ++ (referenceChunk 12 (lowerBound 100 12) (upperBound 999 12 + 1 - lowerBound 100 12) ++ (referenceChunk 13 (lowerBound 100 13) (upperBound 999 13 + 1 - lowerBound 100 13) ++ (referenceChunk 14 (lowerBound 100 14) (upperBound 999 14 + 1 - lowerBound 100 14) ++ (referenceChunk 15 (lowerBound 100 15) (upperBound 999 15 + 1 - lowerBound 100 15) ++ (referenceChunk 16 (lowerBound 100 16) (upperBound 999 16 + 1 - lowerBound 100 16) ++ (referenceChunk 17 (lowerBound 100 17) (upperBound 999 17 + 1 - lowerBound 100 17) ++ (referenceChunk 18 (lowerBound 100 18) (upperBound 999 18 + 1 - lowerBound 100 18) ++ (referenceChunk 19 (lowerBound 100 19) (upperBound 999 19 + 1 - lowerBound 100 19) ++ (referenceChunk 20 (lowerBound 100 20) (upperBound 999 20 + 1 - lowerBound 100 20) ++ (referenceChunk 21 (lowerBound 100 21) (upperBound 999 21 + 1 - lowerBound 100 21) ++ (referenceChunk 22 (lowerBound 100 22) (upperBound 999 22 + 1 - lowerBound 100 22) ++ (referenceChunk 23 (lowerBound 100 23) (upperBound 999 23 + 1 - lowerBound 100 23) ++ (referenceChunk 24 (lowerBound 100 24) (upperBound 999 24 + 1 - lowerBound 100 24) ++ (referenceChunk 25 (lowerBound 100 25) (upperBound 999 25 + 1 - lowerBound 100 25) ++ (referenceChunk 26 (lowerBound 100 26) (upperBound 999 26 + 1 - lowerBound 100 26) ++ (referenceChunk 27 (lowerBound 100 27) (upperBound 999 27 + 1 - lowerBound 100 27) ++ (referenceChunk 28 (lowerBound 100 28) (upperBound 999 28 + 1 - lowerBound 100 28) ++ (referenceChunk 29 (lowerBound 100 29) (upperBound 999 29 + 1 - lowerBound 100 29) ++ (referenceChunk 30 (lowerBound 100 30) (upperBound 999 30 + 1 - lowerBound 100 30) ++ (referenceChunk 31 (lowerBound 100 31) (upperBound 999 31 + 1 - lowerBound 100 31) ++ (referenceChunk 32 (lowerBound 100 32) (upperBound 999 32 + 1 - lowerBound 100 32) ++ (referenceChunk 33 (lowerBound 100 33) (upperBound 999 33 + 1 - lowerBound 100 33) ++ (referenceChunk 34 (lowerBound 100 34) (upperBound 999 34 + 1 - lowerBound 100 34) ++ (referenceChunk 35 (lowerBound 100 35) (upperBound 999 35 + 1 - lowerBound 100 35) ++ (referenceChunk 36 (lowerBound 100 36) (upperBound 999 36 + 1 - lowerBound 100 36) ++ (referenceChunk 37 (lowerBound 100 37) (upperBound 999 37 + 1 - lowerBound 100 37) ++ (referenceChunk 38 (lowerBound 100 38) (upperBound 999 38 + 1 - lowerBound 100 38) ++ (referenceChunk 39 (lowerBound 100 39) (upperBound 999 39 + 1 - lowerBound 100 39) ++ (referenceChunk 40 (lowerBound 100 40) (upperBound 999 40 + 1 - lowerBound 100 40) ++ (referenceChunk 41 (lowerBound 100 41) (upperBound 999 41 + 1 - lowerBound 100 41) ++ (referenceChunk 42 (lowerBound 100 42) (upperBound 999 42 + 1 - lowerBound 100 42) ++ (referenceChunk 43 (lowerBound 100 43) (upperBound 999 43 + 1 - lowerBound 100 43) ++ (referenceChunk 44 (lowerBound 100 44) (upperBound 999 44 + 1 - lowerBound 100 44) ++ (referenceChunk 45 (lowerBound 100 45) (upperBound 999 45 + 1 - lowerBound 100 45) ++ (referenceChunk 46 (lowerBound 100 46) (upperBound 999 46 + 1 - lowerBound 100 46) ++ (referenceChunk 47 (lowerBound 100 47) (upperBound 999 47 + 1 - lowerBound 100 47) ++ (referenceChunk 48 (lowerBound 100 48) (upperBound 999 48 + 1 - lowerBound 100 48) ++ (referenceChunk 49 (lowerBound 100 49) (upperBound 999 49 + 1 - lowerBound 100 49) ++ (referenceChunk 50 (lowerBound 100 50) (upperBound 999 50 + 1 - lowerBound 100 50) ++ (referenceChunk 51 (lowerBound 100 51) (upperBound 999 51 + 1 - lowerBound 100 51) ++ (referenceChunk 52 (lowerBound 100 52) (upperBound 999 52 + 1 - lowerBound 100 52) ++ (referenceChunk 53 (lowerBound 100 53) (upperBound 999 53 + 1 - lowerBound 100 53) ++ (referenceChunk 54 (lowerBound 100 54) (upperBound 999 54 + 1 - lowerBound 100 54) ++ (referenceChunk 55 (lowerBound 100 55) (upperBound 999 55 + 1 - lowerBound 100 55) ++ (referenceChunk 56 (lowerBound 100 56) (upperBound 999 56 + 1 - lowerBound 100 56) ++ (referenceChunk 57 (lowerBound 100 57) (upperBound 999 57 + 1 - lowerBound 100 57) ++ (referenceChunk 58 (lowerBound 100 58) (upperBound 999 58 + 1 - lowerBound 100 58) ++ (referenceChunk 59 (lowerBound 100 59) (upperBound 999 59 + 1 - lowerBound 100 59) ++ (referenceChunk 60 (lowerBound 100 60) (upperBound 999 60 + 1 - lowerBound 100 60) ++ (referenceChunk 61 (lowerBound 100 61) (upperBound 999 61 + 1 - lowerBound 100 61) ++ (referenceChunk 62 (lowerBound 100 62) (upperBound 999 62 + 1 - lowerBound 100 62) ++ (referenceChunk 63 (lowerBound 100 63) (upperBound 999 63 + 1 - lowerBound 100 63) ++ (referenceChunk 64 (lowerBound 100 64) (upperBound 999 64 + 1 - lowerBound 100 64) ++ (referenceChunk 65 (lowerBound 100 65) (upperBound 999 65 + 1 - lowerBound 100 65) ++ (referenceChunk 66 (lowerBound 100 66) (upperBound 999 66 + 1 - lowerBound 100 66) ++ (referenceChunk 67 (lowerBound 100 67) (upperBound 999 67 + 1 - lowerBound 100 67) ++ (referenceChunk 68 (lowerBound 100 68) (upperBound 999 68 + 1 - lowerBound 100 68) ++ (referenceChunk 69 (lowerBound 100 69) (upperBound 999 69 + 1 - lowerBound 100 69) ++ (referenceChunk 70 (lowerBound 100 70) (upperBound 999 70 + 1 - lowerBound 100 70) ++ (referenceChunk 71 (lowerBound 100 71) (upperBound 999 71 + 1 - lowerBound 100 71) ++ (referenceChunk 72 (lowerBound 100 72) (upperBound 999 72 + 1 - lowerBound 100 72) ++ (referenceChunk 73 (lowerBound 100 73) (upperBound 999 73 + 1 - lowerBound 100 73) ++ (referenceChunk 74 (lowerBound 100 74) (upperBound 999 74 + 1 - lowerBound 100 74) ++ (referenceChunk 75 (lowerBound 100 75) (upperBound 999 75 + 1 - lowerBound 100 75) ++ (referenceChunk 76 (lowerBound 100 76) (upperBound 999 76 + 1 - lowerBound 100 76) ++ (referenceChunk 77 (lowerBound 100 77) (upperBound 999 77 + 1 - lowerBound 100 77) ++ (referenceChunk 78 (lowerBound 100 78) (upperBound 999 78 + 1 - lowerBound 100 78) ++ (referenceChunk 79 (lowerBound 100 79) (upperBound 999 79 + 1 - lowerBound 100 79) ++ (referenceChunk 80 (lowerBound 100 80) (upperBound 999 80 + 1 - lowerBound 100 80) ++ (referenceChunk 81 (lowerBound 100 81) (upperBound 999 81 + 1 - lowerBound 100 81) ++ (referenceChunk 82 (lowerBound 100 82) (upperBound 999 82 + 1 - lowerBound 100 82) ++ (referenceChunk 83 (lowerBound 100 83) (upperBound 999 83 + 1 - lowerBound 100 83) ++ (referenceChunk 84 (lowerBound 100 84) (upperBound 999 84 + 1 - lowerBound 100 84) ++ (referenceChunk 85 (lowerBound 100 85) (upperBound 999 85 + 1 - lowerBound 100 85) ++ (referenceChunk 86 (lowerBound 100 86) (upperBound 999 86 + 1 - lowerBound 100 86) ++ (referenceChunk 87 (lowerBound 100 87) (upperBound 999 87 + 1 - lowerBound 100 87) ++ (referenceChunk 88 (lowerBound 100 88) (upperBound 999 88 + 1 - lowerBound 100 88) ++ (referenceChunk 89 (lowerBound 100 89) (upperBound 999 89 + 1 - lowerBound 100 89) ++ (referenceChunk 90 (lowerBound 100 90) (upperBound 999 90 + 1 - lowerBound 100 90) ++ (referenceChunk 91 (lowerBound 100 91) (upperBound 999 91 + 1 - lowerBound 100 91) ++ (referenceChunk 92 (lowerBound 100 92) (upperBound 999 92 + 1 - lowerBound 100 92) ++ (referenceChunk 93 (lowerBound 100 93) (upperBound 999 93 + 1 - lowerBound 100 93) ++ (referenceChunk 94 (lowerBound 100 94) (upperBound 999 94 + 1 - lowerBound 100 94) ++ (referenceChunk 95 (lowerBound 100 95) (upperBound 999 95 + 1 - lowerBound 100 95) ++ (referenceChunk 96 (lowerBound 100 96) (upperBound 999 96 + 1 - lowerBound 100 96) ++ (referenceChunk 97 (lowerBound 100 97) (upperBound 999 97 + 1 - lowerBound 100 97) ++ (referenceChunk 98 (lowerBound 100 98) (upperBound 999 98 + 1 - lowerBound 100 98) ++ (referenceChunk 99 (lowerBound 100 99) (upperBound 999 99 + 1 - lowerBound 100 99) ++ [])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = _
  rewrite [reference_row1, reference_row2, reference_row3, reference_row4, reference_row5, reference_row6, reference_row7, reference_row8, reference_row9, reference_row10, reference_row11, reference_row12, reference_row13, reference_row14, reference_row15, reference_row16, reference_row17, reference_row18, reference_row19, reference_row20, reference_row21, reference_row22, reference_row23, reference_row24, reference_row25, reference_row26, reference_row27, reference_row28, reference_row29, reference_row30, reference_row31, reference_row32, reference_row33, reference_row34, reference_row35, reference_row36, reference_row37, reference_row38, reference_row39, reference_row40, reference_row41, reference_row42, reference_row43, reference_row44, reference_row45, reference_row46, reference_row47, reference_row48, reference_row49, reference_row50, reference_row51, reference_row52, reference_row53, reference_row54, reference_row55, reference_row56, reference_row57, reference_row58, reference_row59, reference_row60, reference_row61, reference_row62, reference_row63, reference_row64, reference_row65, reference_row66, reference_row67, reference_row68, reference_row69, reference_row70, reference_row71, reference_row72, reference_row73, reference_row74, reference_row75, reference_row76, reference_row77, reference_row78, reference_row79, reference_row80, reference_row81, reference_row82, reference_row83, reference_row84, reference_row85, reference_row86, reference_row87, reference_row88, reference_row89, reference_row90, reference_row91, reference_row92, reference_row93, reference_row94, reference_row95, reference_row96, reference_row97, reference_row98, reference_row99]
  rfl

theorem optimized_products : products = productsFound := by
  change (row 1000 9999 1 ++ (row 1000 9999 2 ++ (row 1000 9999 3 ++ (row 1000 9999 4 ++ (row 1000 9999 5 ++ (row 1000 9999 6 ++ (row 1000 9999 7 ++ (row 1000 9999 8 ++ (row 1000 9999 9 ++ []))))))))) ++ (row 100 999 10 ++ (row 100 999 11 ++ (row 100 999 12 ++ (row 100 999 13 ++ (row 100 999 14 ++ (row 100 999 15 ++ (row 100 999 16 ++ (row 100 999 17 ++ (row 100 999 18 ++ (row 100 999 19 ++ (row 100 999 20 ++ (row 100 999 21 ++ (row 100 999 22 ++ (row 100 999 23 ++ (row 100 999 24 ++ (row 100 999 25 ++ (row 100 999 26 ++ (row 100 999 27 ++ (row 100 999 28 ++ (row 100 999 29 ++ (row 100 999 30 ++ (row 100 999 31 ++ (row 100 999 32 ++ (row 100 999 33 ++ (row 100 999 34 ++ (row 100 999 35 ++ (row 100 999 36 ++ (row 100 999 37 ++ (row 100 999 38 ++ (row 100 999 39 ++ (row 100 999 40 ++ (row 100 999 41 ++ (row 100 999 42 ++ (row 100 999 43 ++ (row 100 999 44 ++ (row 100 999 45 ++ (row 100 999 46 ++ (row 100 999 47 ++ (row 100 999 48 ++ (row 100 999 49 ++ (row 100 999 50 ++ (row 100 999 51 ++ (row 100 999 52 ++ (row 100 999 53 ++ (row 100 999 54 ++ (row 100 999 55 ++ (row 100 999 56 ++ (row 100 999 57 ++ (row 100 999 58 ++ (row 100 999 59 ++ (row 100 999 60 ++ (row 100 999 61 ++ (row 100 999 62 ++ (row 100 999 63 ++ (row 100 999 64 ++ (row 100 999 65 ++ (row 100 999 66 ++ (row 100 999 67 ++ (row 100 999 68 ++ (row 100 999 69 ++ (row 100 999 70 ++ (row 100 999 71 ++ (row 100 999 72 ++ (row 100 999 73 ++ (row 100 999 74 ++ (row 100 999 75 ++ (row 100 999 76 ++ (row 100 999 77 ++ (row 100 999 78 ++ (row 100 999 79 ++ (row 100 999 80 ++ (row 100 999 81 ++ (row 100 999 82 ++ (row 100 999 83 ++ (row 100 999 84 ++ (row 100 999 85 ++ (row 100 999 86 ++ (row 100 999 87 ++ (row 100 999 88 ++ (row 100 999 89 ++ (row 100 999 90 ++ (row 100 999 91 ++ (row 100 999 92 ++ (row 100 999 93 ++ (row 100 999 94 ++ (row 100 999 95 ++ (row 100 999 96 ++ (row 100 999 97 ++ (row 100 999 98 ++ (row 100 999 99 ++ [])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = _
  rewrite [optimized_row1, optimized_row2, optimized_row3, optimized_row4, optimized_row5, optimized_row6, optimized_row7, optimized_row8, optimized_row9, optimized_row10, optimized_row11, optimized_row12, optimized_row13, optimized_row14, optimized_row15, optimized_row16, optimized_row17, optimized_row18, optimized_row19, optimized_row20, optimized_row21, optimized_row22, optimized_row23, optimized_row24, optimized_row25, optimized_row26, optimized_row27, optimized_row28, optimized_row29, optimized_row30, optimized_row31, optimized_row32, optimized_row33, optimized_row34, optimized_row35, optimized_row36, optimized_row37, optimized_row38, optimized_row39, optimized_row40, optimized_row41, optimized_row42, optimized_row43, optimized_row44, optimized_row45, optimized_row46, optimized_row47, optimized_row48, optimized_row49, optimized_row50, optimized_row51, optimized_row52, optimized_row53, optimized_row54, optimized_row55, optimized_row56, optimized_row57, optimized_row58, optimized_row59, optimized_row60, optimized_row61, optimized_row62, optimized_row63, optimized_row64, optimized_row65, optimized_row66, optimized_row67, optimized_row68, optimized_row69, optimized_row70, optimized_row71, optimized_row72, optimized_row73, optimized_row74, optimized_row75, optimized_row76, optimized_row77, optimized_row78, optimized_row79, optimized_row80, optimized_row81, optimized_row82, optimized_row83, optimized_row84, optimized_row85, optimized_row86, optimized_row87, optimized_row88, optimized_row89, optimized_row90, optimized_row91, optimized_row92, optimized_row93, optimized_row94, optimized_row95, optimized_row96, optimized_row97, optimized_row98, optimized_row99]
  rfl

theorem answer : productsFound.eraseDups.sum = 45228 := by decide +kernel

end ProjectEulerStatements.PandigitalCertificate
