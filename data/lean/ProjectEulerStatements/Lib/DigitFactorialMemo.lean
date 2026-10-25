import ProjectEulerStatements.Lib.DigitFactorialOrbits

/-! Correct complete caches are preserved by cycle batches and reverse tail writes. -/
namespace ProjectEulerStatements.DigitFactorialChains.Memo
open BoundedOrbit
set_option Elab.async false

abbrev Cache := Nat → Option Nat
def Has (cache : Cache) (n : Nat) : Prop := ∃ length, cache n = some length

structure Valid (cache : Cache) : Prop where
  correct : ∀ n length, cache n = some length → chainLen n = length
  closed : ∀ n, Has cache n → Has cache (nextTerm n)

theorem empty_valid : Valid (fun _ => none) where
  correct := by intro n length impossible; cases impossible
  closed := by rintro n ⟨length, impossible⟩; cases impossible

def write (cache : Cache) (n length : Nat) : Cache :=
  fun key => if key = n then some length else cache key

theorem has_write (cache : Cache) (n length key : Nat) :
    Has (write cache n length) key ↔ key = n ∨ Has cache key := by
  by_cases same : key = n <;> simp [Has, write, same]

/-- Closed cache domains contain the entire orbit of every stored key. -/
theorem Valid.orbit_known {cache : Cache} (valid : Valid cache) (n : Nat)
    (known : Has cache n) : ∀ value ∈ orbit n, Has cache value :=
  orbit_within n (Has cache) known valid.closed

theorem Valid.write_tail {cache : Cache} (valid : Valid cache) (n remaining : Nat)
    (fresh : cache n = none) (following : cache (nextTerm n) = some remaining) :
    Valid (write cache n (remaining + 1)) := by
  have outside : ¬ Has cache n := by rintro ⟨length, found⟩; simp [fresh] at found
  have correct : chainLen n = remaining + 1 := by
    rw [chainLen_of_fresh n (Has cache) outside ⟨remaining, following⟩ valid.closed,
      valid.correct _ _ following]
  constructor
  · intro key length found
    by_cases same : key = n
    · subst key
      have equal : remaining + 1 = length := by simpa [write] using found
      exact correct.trans equal
    · exact valid.correct key length (by simpa only [write, if_neg same] using found)
  · intro key known
    apply (has_write cache n (remaining + 1) (nextTerm key)).mpr
    rcases (has_write cache n (remaining + 1) key).mp known with rfl | before
    · exact Or.inr ⟨remaining, following⟩
    · exact Or.inr (valid.closed key before)

def addCycle (cache : Cache) (cycle : List Nat) (length : Nat) : Cache :=
  fun key => if key ∈ cycle then some length else cache key

theorem has_addCycle (cache : Cache) (cycle : List Nat) (length key : Nat) :
    Has (addCycle cache cycle length) key ↔ key ∈ cycle ∨ Has cache key := by
  by_cases member : key ∈ cycle <;> simp [Has, addCycle, member]

/-- The cycle batch is complete before the preceding tail is filled. -/
theorem Valid.with_cycle {cache : Cache} (valid : Valid cache) (cycle : List Nat)
    (length : Nat) (correct : ∀ n ∈ cycle, chainLen n = length)
    (closed : ∀ n ∈ cycle, nextTerm n ∈ cycle) : Valid (addCycle cache cycle length) := by
  constructor
  · intro key value found
    by_cases member : key ∈ cycle
    · have equal : length = value := by
        simpa only [addCycle, if_pos member, Option.some.injEq] using found
      exact (correct key member).trans equal
    · exact valid.correct key value (by simpa only [addCycle, if_neg member] using found)
  · intro key known
    apply (has_addCycle cache cycle length (nextTerm key)).mpr
    rcases (has_addCycle cache cycle length key).mp known with member | before
    · exact Or.inl (closed key member)
    · exact Or.inr (valid.closed key before)

theorem Valid.add_periodic_cycle {cache : Cache} (valid : Valid cache)
    (start count : Nat) (positive : 0 < count)
    (periodic : nextTerm^[count] start = start)
    (distinct : (segment nextTerm start count).Nodup) :
    Valid (addCycle cache (segment nextTerm start count) count) :=
  valid.with_cycle _ count (chainLen_of_cycle start count · positive periodic distinct)
    (cycle_closed start count positive periodic)

end ProjectEulerStatements.DigitFactorialChains.Memo
