import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Least-prime producers and the early exits of the linear totient sieve. -/
namespace ProjectEulerStatements.TotientLinearSieve
set_option Elab.async false

/-- The outer iteration which produces a composite number. -/
def producer (n : Nat) : Nat := n / n.minFac

theorem producer_lt (n : Nat) (large : 2 ≤ n) : producer n < n := by
  exact Nat.div_lt_self (by omega) (Nat.minFac_prime (by omega)).one_lt

theorem minFac_mul (i p : Nat) (large : 2 ≤ i) (prime : Nat.Prime p)
    (first : p ≤ i.minFac) : (i * p).minFac = p := by
  apply le_antisymm (Nat.minFac_le_of_dvd prime.two_le (dvd_mul_left p i))
  apply (Nat.le_minFac.mpr ?_).resolve_left (by nlinarith [prime.two_le])
  intro q primeQ divides
  rcases primeQ.dvd_mul.mp divides with dividesI | dividesP
  · exact first.trans (Nat.minFac_le_of_dvd primeQ.two_le dividesI)
  · have same : q = p := ((prime.dvd_iff_eq primeQ.ne_one).mp dividesP).symm
    omega

theorem producer_mul (i p : Nat) (large : 2 ≤ i) (prime : Nat.Prime p)
    (first : p ≤ i.minFac) : producer (i * p) = i := by
  rw [producer, minFac_mul i p large prime first, Nat.mul_div_cancel _ prime.pos]

/-- Every composite is written by its quotient and its least prime factor. -/
theorem composite_producer (n : Nat) (large : 2 ≤ n) (composite : ¬ Nat.Prime n) :
    2 ≤ producer n ∧ Nat.Prime n.minFac ∧ n.minFac ≤ (producer n).minFac ∧
      producer n * n.minFac = n := by
  have prime := Nat.minFac_prime (n := n) (by omega)
  have bounded := Nat.minFac_le_div (by omega : 0 < n) composite
  have product : producer n * n.minFac = n := Nat.div_mul_cancel (Nat.minFac_dvd n)
  have largeProducer : 2 ≤ producer n := prime.two_le.trans bounded
  refine ⟨largeProducer, prime, ?_, product⟩
  apply (Nat.le_minFac.mpr ?_).resolve_left (by omega)
  intro q primeQ divides
  exact Nat.minFac_le_of_dvd primeQ.two_le (divides.trans ⟨n.minFac, product.symm⟩)

/-- Multiplication by an eligible prime takes exactly the branch used by the sieve. -/
theorem product_totient (i p : Nat) (prime : Nat.Prime p) :
    (i * p).totient = if i % p = 0 then i.totient * p else i.totient * (p - 1) := by
  by_cases divides : i % p = 0
  · rw [if_pos divides, Nat.mul_comm i p,
      Nat.totient_mul_of_prime_of_dvd prime (Nat.dvd_of_mod_eq_zero divides), Nat.mul_comm]
  · rw [if_neg divides, Nat.mul_comm i p,
      Nat.totient_mul_of_prime_of_not_dvd prime (by simpa [Nat.dvd_iff_mod_eq_zero] using divides),
      Nat.mul_comm]

abbrev Cell := Nat × Bool
abbrev Table := Nat → Cell

/-- Each product write stores its totient and marks it composite. -/
def write (i p : Nat) (table : Table) : Table :=
  Function.update table (i * p)
    (if i % p = 0 then ((table i).1 * p, true) else ((table i).1 * (p - 1), true))

def pass (limit i : Nat) : List Nat → Table → Table
  | [], table => table
  | p :: rest, table =>
      if limit < i * p then table
      else if i % p = 0 then write i p table
      else pass limit i rest (write i p table)

/-- The source's two early exits visit exactly these products. -/
def Target (limit i : Nat) (cache : List Nat) (n : Nat) : Prop :=
  n ≤ limit ∧ ∃ p ∈ cache, p ≤ i.minFac ∧ n = i * p

instance (limit i : Nat) (cache : List Nat) (n : Nat) :
    Decidable (Target limit i cache n) := inferInstanceAs
      (Decidable (n ≤ limit ∧ ∃ p ∈ cache, p ≤ i.minFac ∧ n = i * p))

theorem write_current (i p : Nat) (large : 2 ≤ i) (prime : Nat.Prime p)
    (table : Table) : write i p table i = table i := by
  have different : i ≠ i * p := by nlinarith [prime.two_le]
  simp [write, Function.update_of_ne different]

theorem write_lookup (i p n : Nat) (prime : Nat.Prime p) (table : Table)
    (correct : (table i).1 = i.totient) :
    write i p table n = if n = i * p then (n.totient, true) else table n := by
  by_cases same : n = i * p
  · subst n
    simp only [write, Function.update_self, correct, if_true, product_totient i p prime]
    split <;> rfl
  · simp [write, same]

theorem pass_lookup (limit i n : Nat) (cache : List Nat) (table : Table)
    (large : 2 ≤ i) (ordered : cache.Pairwise (· < ·))
    (primes : ∀ p ∈ cache, Nat.Prime p) (complete : i.minFac ∈ cache)
    (correct : (table i).1 = i.totient) :
    pass limit i cache table n =
      if Target limit i cache n then (n.totient, true) else table n := by
  induction cache generalizing table with
  | nil => simp at complete
  | cons p rest ih =>
      obtain ⟨after, orderedRest⟩ := List.pairwise_cons.mp ordered
      have prime := primes p (by simp)
      have primesRest : ∀ q ∈ rest, Nat.Prime q := fun q member => primes q (by simp [member])
      have first : p ≤ i.minFac := by
        rcases List.mem_cons.mp complete with equal | member
        · omega
        · exact (after i.minFac member).le
      by_cases outside : limit < i * p
      · have absent : ¬ Target limit i (p :: rest) n := by
          rintro ⟨bounded, q, member, _, rfl⟩
          rcases List.mem_cons.mp member with rfl | member
          · omega
          · have larger := after q member
            nlinarith
        simp [pass, outside, absent]
      · have bounded : i * p ≤ limit := by omega
        by_cases divides : i % p = 0
        · have equal : p = i.minFac :=
            le_antisymm first (Nat.minFac_le_of_dvd prime.two_le
              (Nat.dvd_of_mod_eq_zero divides))
          have target : Target limit i (p :: rest) n ↔ n = i * p := by
            constructor
            · rintro ⟨_, q, member, atMost, value⟩
              rcases List.mem_cons.mp member with rfl | member
              · exact value
              · have larger := after q member
                omega
            · intro same
              exact ⟨same ▸ bounded, p, by simp, first, same⟩
          simp only [pass, if_neg outside, if_pos divides, write_lookup i p n prime table correct,
            target]
        · have completeRest : i.minFac ∈ rest := by
            rcases List.mem_cons.mp complete with equal | member
            · have factor : p ∣ i := equal ▸ Nat.minFac_dvd i
              exact False.elim (divides (Nat.mod_eq_zero_of_dvd factor))
            · exact member
          have continued := ih (write i p table) orderedRest primesRest completeRest
            (by simpa only [write_current i p large prime table] using correct)
          have target : Target limit i (p :: rest) n ↔
              n = i * p ∨ Target limit i rest n := by
            constructor
            · rintro ⟨bound, q, member, atMost, value⟩
              rcases List.mem_cons.mp member with rfl | member
              · exact Or.inl value
              · exact Or.inr ⟨bound, q, member, atMost, value⟩
            · rintro (same | ⟨bound, q, member, atMost, value⟩)
              · exact ⟨same ▸ bounded, p, by simp, first, same⟩
              · exact ⟨bound, q, by simp [member], atMost, value⟩
          simp only [pass, if_neg outside, if_neg divides, continued,
            write_lookup i p n prime table correct, target]
          by_cases tail : Target limit i rest n <;> by_cases head : n = i * p <;>
            simp [tail, head]

/-- A complete prime cache gives precisely one producer for each composite. -/
theorem target_iff (limit i n : Nat) (cache : List Nat) (large : 2 ≤ i)
    (complete : ∀ p, p ∈ cache ↔ Nat.Prime p ∧ p ≤ i) :
    Target limit i cache n ↔
      n ≤ limit ∧ 2 ≤ n ∧ ¬ Nat.Prime n ∧ producer n = i := by
  constructor
  · rintro ⟨bounded, p, member, first, rfl⟩
    have prime := ((complete p).mp member).1
    exact ⟨bounded, by nlinarith [prime.two_le],
      Nat.not_prime_mul (by omega) prime.ne_one, producer_mul i p large prime first⟩
  · rintro ⟨bounded, largeN, composite, produced⟩
    obtain ⟨_, prime, first, product⟩ := composite_producer n largeN composite
    rw [produced] at first product
    refine ⟨bounded, n.minFac, (complete n.minFac).mpr ⟨prime, ?_⟩, first, product.symm⟩
    exact first.trans (Nat.minFac_le (by omega))

/-- A cell before an outer iteration records exactly the earlier producers and primes. -/
def expected (next n : Nat) : Cell :=
  if n = 1 then (1, false)
  else if Nat.Prime n then (if n < next then n - 1 else 0, false)
  else if 2 ≤ n ∧ producer n < next then (n.totient, true) else (0, false)

/-- The primality test reads a completed cell at the current index. -/
theorem expected_current (i : Nat) (large : 2 ≤ i) :
    expected i i = if Nat.Prime i then (0, false) else (i.totient, true) := by
  have earlier := producer_lt i large
  simp [expected, show i ≠ 1 by omega, large, earlier]

/-- Prime initialization affects only the current index. -/
def prepare (i : Nat) (table : Table) : Table :=
  if (table i).2 then table else Function.update table i (i - 1, false)

theorem prepare_current (i : Nat) (large : 2 ≤ i) (table : Table)
    (current : table i = expected i i) : (prepare i table i).1 = i.totient := by
  rw [expected_current i large] at current
  by_cases prime : Nat.Prime i
  · simp only [prime, if_true] at current
    simp [prepare, current, Nat.totient_prime prime]
  · simp only [prime, if_false] at current
    simp [prepare, current]

theorem prepare_lookup (i n : Nat) (large : 2 ≤ i) (table : Table)
    (current : table i = expected i i) :
    prepare i table n = if n = i ∧ Nat.Prime i then (i.totient, false) else table n := by
  rw [expected_current i large] at current
  by_cases prime : Nat.Prime i
  · simp only [prime, if_true] at current
    simp [prepare, current, prime, Nat.totient_prime prime, Function.update_apply]
  · simp only [prime, if_false] at current
    simp [prepare, current, prime]

/-- The sieve's initialized tables have no composite producers before iteration two. -/
theorem expected_initial (n : Nat) : expected 2 n = if n = 1 then (1, false) else (0, false) := by
  by_cases one : n = 1
  · simp [expected, one]
  · by_cases prime : Nat.Prime n
    · have large := prime.two_le
      simp [expected, one, prime, show ¬ n < 2 by omega]
    · have absent : ¬ (2 ≤ n ∧ producer n < 2) := by
        rintro ⟨large, early⟩
        have produced := (composite_producer n large prime).1
        omega
      simp only [expected, if_neg one, if_neg prime, if_neg absent]

/-- Advancing an outer iteration adds only its prime and its composite products. -/
theorem expected_step (i n : Nat) (large : 2 ≤ i) :
    expected (i + 1) n =
      if 2 ≤ n ∧ ¬ Nat.Prime n ∧ producer n = i then (n.totient, true)
      else if n = i ∧ Nat.Prime i then (i.totient, false) else expected i n := by
  by_cases one : n = 1
  · subst n
    simp [expected, show (1 : Nat) ≠ i by omega]
  · by_cases prime : Nat.Prime n
    · have lower := prime.two_le
      by_cases same : n = i
      · subst n
        simp [expected, one, prime, Nat.totient_prime prime]
      · by_cases before : n < i
        · simp [expected, one, prime, same, before, show n < i + 1 by omega]
        · simp [expected, one, prime, same, before, show ¬ n < i + 1 by omega]
    · by_cases small : n < 2
      · have zero : n = 0 := by omega
        subst n
        simp [expected, producer, show (0 : Nat) ≠ i by omega]
      · have largeN : 2 ≤ n := by omega
        have notCurrentPrime : ¬ (n = i ∧ Nat.Prime i) := by rintro ⟨rfl, h⟩; exact prime h
        by_cases produced : producer n = i
        · simp [expected, one, prime, largeN, produced]
        · have same : (producer n < i + 1) ↔ producer n < i := by omega
          simp [expected, one, prime, largeN, produced, notCurrentPrime, same]

/-- The actual bounded product pass advances the complete table invariant. -/
theorem step_correct (limit i : Nat) (cache : List Nat) (table : Table)
    (large : 2 ≤ i) (within : i ≤ limit) (ordered : cache.Pairwise (· < ·))
    (complete : ∀ p, p ∈ cache ↔ Nat.Prime p ∧ p ≤ i)
    (correct : ∀ n, n ≤ limit → table n = expected i n) :
    ∀ n, n ≤ limit → pass limit i cache (prepare i table) n = expected (i + 1) n := by
  have current := correct i within
  have primes : ∀ p ∈ cache, Nat.Prime p := fun p member => ((complete p).mp member).1
  have covered : i.minFac ∈ cache :=
    (complete i.minFac).mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_le (by omega)⟩
  intro n bounded
  rw [pass_lookup limit i n cache (prepare i table) large ordered primes covered
    (prepare_current i large table current)]
  simp only [target_iff limit i n cache large complete, bounded, true_and]
  rw [prepare_lookup i n large table current, correct n bounded, expected_step i n large]

/-- A completed finite table stores every mathematical totient. -/
theorem expected_finished (limit n : Nat) (bounded : n ≤ limit) :
    (expected (limit + 1) n).1 = n.totient := by
  by_cases one : n = 1
  · subst n
    simp [expected]
  · by_cases prime : Nat.Prime n
    · simp [expected, one, prime, show n < limit + 1 by omega, Nat.totient_prime prime]
    · by_cases large : 2 ≤ n
      · have early := producer_lt n large
        simp [expected, one, prime, large, show producer n < limit + 1 by omega]
      · have zero : n = 0 := by omega
        subst n
        simp [expected]

/-- The increasing prime cache available after testing the current index. -/
def primeCache (i : Nat) : List Nat :=
  (List.range (i + 1)).filter (fun p => decide (Nat.Prime p))

theorem primeCache_complete (i p : Nat) :
    p ∈ primeCache i ↔ Nat.Prime p ∧ p ≤ i := by
  simp only [primeCache, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun ⟨bound, prime⟩ => ⟨prime, by omega⟩, fun ⟨prime, bound⟩ => ⟨by omega, prime⟩⟩

theorem primeCache_ordered (i : Nat) : (primeCache i).Pairwise (· < ·) := by
  exact (List.pairwise_lt_range (n := i + 1)).filter _

def step (limit i : Nat) (table : Table) : Table :=
  pass limit i (primeCache i) (prepare i table)

/-- Finite outer iterations, with their count derived from the inclusive input bound. -/
def run (limit : Nat) : Nat → Nat → Table → Table
  | _, 0, table => table
  | i, count + 1, table => run limit (i + 1) count (step limit i table)

theorem run_correct (limit i count : Nat) (table : Table) (large : 2 ≤ i)
    (within : i + count ≤ limit + 1)
    (correct : ∀ n, n ≤ limit → table n = expected i n) :
    ∀ n, n ≤ limit → run limit i count table n = expected (i + count) n := by
  induction count generalizing i table with
  | zero => simpa only [run, Nat.add_zero] using correct
  | succ count ih =>
      have advanced := step_correct limit i (primeCache i) table large (by omega)
        (primeCache_ordered i) (primeCache_complete i) correct
      have continued := ih (i + 1) (step limit i table) (by omega) (by omega) advanced
      simpa only [run, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using continued

def initial : Table := fun n => if n = 1 then (1, false) else (0, false)

def table (limit : Nat) : Table := run limit 2 (limit - 1) initial

/-- The linear sieve computes totients for every inclusive natural bound. -/
theorem table_totient (limit n : Nat) (bounded : n ≤ limit) :
    (table limit n).1 = n.totient := by
  by_cases positive : 1 ≤ limit
  · have count : 2 + (limit - 1) = limit + 1 := by omega
    have result := run_correct limit 2 (limit - 1) initial (by decide) (by omega)
      (fun k _ => (expected_initial k).symm) n bounded
    rw [count] at result
    exact (congrArg Prod.fst result).trans (expected_finished limit n bounded)
  · have zeroLimit : limit = 0 := by omega
    have zeroN : n = 0 := by omega
    subst limit n
    simp [table, run, initial]

end ProjectEulerStatements.TotientLinearSieve
