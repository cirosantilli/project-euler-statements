import ProjectEulerStatements.P14

/-! Collatz arithmetic and cache invariants, conditional on the statement's
existing universal convergence axiom. No additional axiom is introduced here. -/
namespace ProjectEulerStatements.Collatz
open ProjectEulerStatements.P14

/-- The signed arithmetic used by Python's single-step helper. -/
def stepInt (n : Int) : Int := if n % 2 = 0 then n / 2 else 3 * n + 1

theorem stepInt_nat (n : Nat) : stepInt n = (collatzStep n : Int) := by
  simp only [stepInt, collatzStep]
  norm_cast
  split <;> rfl

@[simp] theorem length_zero : collatzLen 0 = 0 := by
  rw [collatzLen.eq_1]
  simp

@[simp] theorem length_one : collatzLen 1 = 1 := by
  rw [collatzLen.eq_1]
  simp

theorem length_step (n : Nat) (positive : 0 < n) (notOne : n ≠ 1) :
    collatzLen n = collatzLen (collatzStep n) + 1 := by
  rw [collatzLen.eq_1]
  simp [show n ≠ 0 by omega, notOne, Nat.add_comm]

theorem length_positive (n : Nat) (positive : 0 < n) : 0 < collatzLen n := by
  by_cases one : n = 1
  · simp [one]
  · rw [length_step n positive one]
    omega

/-- Zero denotes a cache miss; every nonzero cache entry is the exact chain length. -/
def CachedLength (n length : Nat) : Prop := length = 0 ∨ length = collatzLen n

theorem CachedLength.hit {n length : Nat} (valid : CachedLength n length)
    (hit : length ≠ 0) : length = collatzLen n :=
  valid.resolve_left hit

/-- Unwinding one visited vertex preserves exactness of a cached suffix length. -/
theorem unwind_length (n suffixLength : Nat) (positive : 0 < n) (notOne : n ≠ 1)
    (suffix : suffixLength = collatzLen (collatzStep n)) :
    suffixLength + 1 = collatzLen n := by
  rw [suffix, length_step n positive notOne]

/-- Function-valued caches make the invariant independent of list/dictionary storage. -/
def ValidCache (cache : Nat → Nat) : Prop := ∀ n, CachedLength n (cache n)

theorem initialCache_valid : ValidCache (fun n => if n = 1 then 1 else 0) := by
  intro n
  by_cases one : n = 1
  · simp [one, CachedLength]
  · simp [one, CachedLength]

theorem ValidCache.update {cache : Nat → Nat} (valid : ValidCache cache)
    (n : Nat) : ValidCache (Function.update cache n (collatzLen n)) := by
  intro m
  by_cases same : m = n
  · subst m
    simp [CachedLength]
  · simpa [Function.update_of_ne same] using valid m

end ProjectEulerStatements.Collatz
