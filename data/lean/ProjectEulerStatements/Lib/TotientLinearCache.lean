import ProjectEulerStatements.Lib.TotientLinearSieve

/-! Ordered prime caches track the composite marks of the linear sieve. -/
namespace ProjectEulerStatements.TotientLinearSieve
set_option Elab.async false

def nextCache (i : Nat) (cache : List Nat) : List Nat :=
  if Nat.Prime i then cache ++ [i] else cache

/-- Testing the current integer advances completeness by exactly one position. -/
theorem nextCache_complete (i : Nat) (cache : List Nat)
    (complete : ∀ p, p ∈ cache ↔ Nat.Prime p ∧ p < i) :
    ∀ p, p ∈ nextCache i cache ↔ Nat.Prime p ∧ p ≤ i := by
  intro p
  by_cases prime : Nat.Prime i
  · simp only [nextCache, if_pos prime, List.mem_append, List.mem_singleton, complete]
    constructor
    · rintro (⟨primeP, before⟩ | rfl)
      · exact ⟨primeP, before.le⟩
      · exact ⟨prime, le_rfl⟩
    · rintro ⟨primeP, bounded⟩
      by_cases same : p = i
      · exact Or.inr same
      · exact Or.inl ⟨primeP, by omega⟩
  · simp only [nextCache, if_neg prime, complete]
    constructor
    · exact fun ⟨primeP, before⟩ => ⟨primeP, before.le⟩
    · rintro ⟨primeP, bounded⟩
      refine ⟨primeP, ?_⟩
      by_contra later
      have same : p = i := by omega
      exact prime (same ▸ primeP)

theorem nextCache_ordered (i : Nat) (cache : List Nat)
    (ordered : cache.Pairwise (· < ·))
    (complete : ∀ p, p ∈ cache ↔ Nat.Prime p ∧ p < i) :
    (nextCache i cache).Pairwise (· < ·) := by
  by_cases prime : Nat.Prime i
  · simp only [nextCache, if_pos prime, List.pairwise_append, List.pairwise_singleton,
      true_and, List.mem_singleton, forall_eq]
    exact ⟨ordered, fun p member => ((complete p).mp member).2⟩
  · simpa only [nextCache, if_neg prime] using ordered

/-- The concrete stored flag and primality agree before the current iteration. -/
theorem expected_mark (i : Nat) (large : 2 ≤ i) :
    (expected i i).2 = !decide (Nat.Prime i) := by
  rw [expected_current i large]
  by_cases prime : Nat.Prime i <;> simp [prime]

end ProjectEulerStatements.TotientLinearSieve
