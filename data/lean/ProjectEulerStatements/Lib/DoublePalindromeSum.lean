import ProjectEulerStatements.Lib.DoublePalindromeEnumeration
import ProjectEulerStatements.Lib.DoublePalindromeBinary

/-! The optimized seed scan sums precisely the reference double palindromes,
including the justification for skipping positive even candidates. -/
namespace ProjectEulerStatements.DoublePalindromes

set_option Elab.async false

private theorem sum_eq_of_nodup_members (left right : List Nat)
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (members : ∀ n, n ∈ left ↔ n ∈ right) : left.sum = right.sum := by
  have same : left.toFinset = right.toFinset := by
    ext n
    simpa using members n
  have first := List.sum_toFinset (fun n : Nat => n) leftNodup
  have second := List.sum_toFinset (fun n : Nat => n) rightNodup
  simp only [List.map_id_fun'] at first second
  rw [same] at first
  exact first.symm.trans second

theorem generate_binary_sum (limit : Nat) (bound : limit ≤ 1000000) :
    ((generate limit).filter (P36.isPalindromeBase 2)).sum = P36.naive limit := by
  rw [naive_filter_sum, filter_sum_without_zero]
  apply sum_eq_of_nodup_members _ _ ((generate_nodup limit).filter _)
    (List.nodup_range.filter _)
  intro n
  simp only [List.mem_filter, mem_generate limit n bound, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq, P36.isDoublePalindrome]
  constructor
  · rintro ⟨⟨positive, inside, decimal⟩, binary⟩
    exact ⟨inside, positive, decimal, binary⟩
  · rintro ⟨inside, positive, decimal, binary⟩
    exact ⟨⟨positive, inside, decimal⟩, binary⟩

def scanStep (total n : Nat) : Nat :=
  if n &&& 1 = 0 then total
  else if P36.isPalindromeBase 2 n then total + n else total

def scan (limit : Nat) : Nat := (generate limit).foldl scanStep 0

theorem scan_filter_sum (items : List Nat) (initial : Nat)
    (positive : ∀ n ∈ items, 0 < n) :
    items.foldl scanStep initial = initial + (items.filter (P36.isPalindromeBase 2)).sum := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
      have headPositive := positive head (by simp)
      have tailPositive : ∀ n ∈ tail, 0 < n := fun n member => positive n (by simp [member])
      by_cases palindrome : P36.isPalindromeBase 2 head = true
      · have parity := positive_palindrome_bitand head headPositive palindrome
        simp [List.foldl, scanStep, parity, palindrome, List.filter, ih _ tailPositive,
          Nat.add_assoc]
      · by_cases even : head &&& 1 = 0 <;>
          simp [List.foldl, scanStep, even, palindrome, List.filter, ih _ tailPositive]

theorem scan_correct (limit : Nat) (bound : limit ≤ 1000000) : scan limit = P36.naive limit := by
  unfold scan
  have positive : ∀ n ∈ generate limit, 0 < n := by
    intro n member
    exact candidate_positive n (List.mem_filter.mp member).1
  rw [scan_filter_sum (generate limit) 0 positive]
  simpa using generate_binary_sum limit bound

end ProjectEulerStatements.DoublePalindromes
