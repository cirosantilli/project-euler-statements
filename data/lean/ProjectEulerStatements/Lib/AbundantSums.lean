import ProjectEulerStatements.P23
import Mathlib.Data.List.Range
import Mathlib.Tactic.IntervalCases

/-! Ordered abundant numbers and the triangular enumeration of their pair sums. -/
namespace ProjectEulerStatements.AbundantSums

theorem twelve_abundant : P23.isAbundant 12 := by decide

theorem twenty_eight_perfect : P23.divisorSum 28 = 28 := by decide

theorem below_twelve (n : Nat) (small : n < 12) : ¬ P23.isAbundant n := by
  interval_cases n <;> decide

def values (limit : Nat) : List Nat :=
  (List.range' 12 (limit - 11)).filter (fun n => decide (P23.isAbundant n))

theorem mem_values (limit n : Nat) : n ∈ values limit ↔ n ∈ P23.abundantSet limit := by
  simp only [values, List.mem_filter, List.mem_range', P23.abundantSet,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨k, bound, rfl⟩, abundant⟩
    exact ⟨⟨by omega, by omega⟩, of_decide_eq_true abundant⟩
  · rintro ⟨⟨lower, upper⟩, abundant⟩
    have large : 12 ≤ n := by
      by_contra small
      exact below_twelve n (by omega) abundant
    exact ⟨⟨n - 12, by omega, by omega⟩, decide_eq_true abundant⟩

theorem values_head (limit : Nat) (large : 12 ≤ limit) : (values limit).head? = some 12 := by
  have count : limit - 11 = (limit - 12) + 1 := by omega
  simp [values, count, List.range'_succ, twelve_abundant]

theorem values_sorted (limit : Nat) : (values limit).Pairwise (· < ·) := by
  exact (List.pairwise_lt_range' (s := 12) (n := limit - 11)).filter _

def row (a : Nat) (items : List Nat) : Finset Nat := items.toFinset.image (a + ·)

@[simp] theorem mem_row (n a : Nat) (items : List Nat) :
    n ∈ row a items ↔ ∃ b ∈ items, a + b = n := by
  simp [row]

def pairs : List Nat → Finset Nat
  | [] => ∅
  | a :: rest => row a (a :: rest) ∪ pairs rest

/-- Visiting each suffix, including its first element, suffices because addition commutes. -/
theorem mem_pairs (n : Nat) (items : List Nat) :
    n ∈ pairs items ↔ ∃ a ∈ items, ∃ b ∈ items, a + b = n := by
  induction items with
  | nil => simp [pairs]
  | cons head tail ih =>
      simp only [pairs, Finset.mem_union, mem_row, ih, List.mem_cons]
      constructor
      · rintro (⟨b, member, sum⟩ | ⟨a, memberA, b, memberB, sum⟩)
        · exact ⟨head, .inl rfl, b, member, sum⟩
        · exact ⟨a, .inr memberA, b, .inr memberB, sum⟩
      · rintro ⟨a, memberA, b, memberB, sum⟩
        rcases memberA with rfl | memberA
        · exact .inl ⟨b, memberB, sum⟩
        · rcases memberB with rfl | memberB
          · exact .inl ⟨a, .inr memberA, by omega⟩
          · exact .inr ⟨a, memberA, b, memberB, sum⟩

theorem pairs_values (limit n : Nat) :
    n ∈ pairs (values limit) ↔ P23.canBeWritten n limit := by
  simp only [mem_pairs, mem_values, P23.canBeWritten]

/-- Once an ordered row exceeds the bound, every later pair sum does too. -/
theorem row_above (a head limit : Nat) (tail : List Nat)
    (ordered : (head :: tail).Pairwise (· < ·)) (large : limit < a + head)
    (n : Nat) (bounded : n ≤ limit) : n ∉ row a (head :: tail) := by
  rw [mem_row]
  rintro ⟨b, member, sum⟩
  rcases List.mem_cons.mp member with rfl | member
  · omega
  · have smaller := (List.pairwise_cons.mp ordered).1 b member
    omega

/-- The final scan adds the indices whose bytes remain zero. -/
def unmarkedSum (marked : Finset Nat) (start count : Nat) : Nat :=
  ((List.range' start count).filter (fun n => decide (n ∉ marked))).sum

theorem unmarkedSum_interval (marked : Finset Nat) (limit : Nat) :
    unmarkedSum marked 1 limit = ((Finset.Icc 1 limit).filter (· ∉ marked)).sum id := by
  have same : ((List.range' 1 limit).filter (fun n => decide (n ∉ marked))).toFinset =
      (Finset.Icc 1 limit).filter (· ∉ marked) := by
    ext n
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range', Finset.mem_filter,
      Finset.mem_Icc]
    constructor
    · rintro ⟨⟨k, bound, rfl⟩, missing⟩
      exact ⟨⟨by omega, by omega⟩, of_decide_eq_true missing⟩
    · rintro ⟨⟨lower, upper⟩, missing⟩
      exact ⟨⟨n - 1, by omega, by omega⟩, decide_eq_true missing⟩
  rw [← same, List.sum_toFinset]
  · simp [unmarkedSum]
  · exact (List.nodup_range' (s := 1) (n := limit)).filter _

theorem unmarkedSum_values (limit : Nat) :
    unmarkedSum (pairs (values limit)) 1 limit = P23.naive limit := by
  classical
  simp only [unmarkedSum_interval, P23.naive, pairs_values, id_eq]

end ProjectEulerStatements.AbundantSums
