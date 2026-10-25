import ProjectEulerStatements.Lib.TotientReference

/-! Input-derived termination and a prime-prefix invariant certify the greedy product scan. -/
namespace ProjectEulerStatements.TotientMaximum
set_option Elab.async false

abbrev Positive := { n : Nat // 0 < n }

def nextProduct (cursor : Nat) (product : Positive) : Positive :=
  if prime : Nat.Prime cursor
  then ⟨product.val * cursor, Nat.mul_pos product.property prime.pos⟩ else product

def scan (limit cursor : Nat) (product : Positive) : Nat :=
  if active : product.val * cursor ≤ limit
  then scan limit (cursor + 2) (nextProduct cursor product) else product.val
termination_by limit + 2 - cursor
decreasing_by
  have positive := product.property
  have lower : cursor ≤ product.val * cursor := by nlinarith
  omega

def optimizedResult (limit : Int) : Nat :=
  if limit < 2 then 1 else scan limit.toNat 3 ⟨2, by decide⟩

theorem nextProduct_value (cursor : Nat) (product : Positive) :
    (nextProduct cursor product).val =
      if Nat.Prime cursor then product.val * cursor else product.val := by
  by_cases prime : Nat.Prime cursor <;> simp only [nextProduct, prime, dite_true, dite_false,
    if_true, if_false]

theorem initial_shape : PrimePrefix 2 3 := by
  refine ⟨Nat.prime_two.squarefree, ?_⟩
  intro p prime
  constructor
  · intro divides
    have upper := Nat.le_of_dvd (by decide : 0 < 2) divides
    omega
  · intro bounded
    have lower := prime.two_le
    have same : p = 2 := by omega
    subst p
    exact dvd_rfl

theorem advance_shape (cursor : Nat) (product : Positive) (large : 3 ≤ cursor)
    (odd : cursor % 2 = 1) (shape : PrimePrefix product.val cursor) :
    PrimePrefix (nextProduct cursor product).val (cursor + 2) := by
  have noBetween (p : Nat) (prime : Nat.Prime p) (bounded : p < cursor + 2) : p ≤ cursor := by
    rcases prime.eq_two_or_odd with two | oddPrime <;> omega
  rw [nextProduct_value]
  by_cases prime : Nat.Prime cursor
  · rw [if_pos prime]
    have absent : ¬ cursor ∣ product.val := by
      intro divides
      have impossible := (shape.factors cursor prime).mp divides
      omega
    have coprime : Nat.Coprime product.val cursor :=
      (prime.coprime_iff_not_dvd.mpr absent).symm
    refine ⟨(Nat.squarefree_mul coprime).mpr ⟨shape.squarefree, prime.squarefree⟩, ?_⟩
    intro p primeP
    rw [primeP.dvd_mul, shape.factors p primeP, prime.dvd_iff_eq primeP.ne_one]
    constructor
    · rintro (earlier | rfl) <;> omega
    · intro bounded
      have upper := noBetween p primeP bounded
      omega
  · rw [if_neg prime]
    refine ⟨shape.squarefree, ?_⟩
    intro p primeP
    rw [shape.factors p primeP]
    constructor
    · omega
    · intro bounded
      have upper := noBetween p primeP bounded
      have different : p ≠ cursor := fun same => prime (same ▸ primeP)
      omega

theorem scan_spec (limit cursor : Nat) (product : Positive) (large : 3 ≤ cursor)
    (odd : cursor % 2 = 1) (bounded : product.val ≤ limit)
    (shape : PrimePrefix product.val cursor) :
    ∃ finalCursor, 0 < scan limit cursor product ∧ scan limit cursor product ≤ limit ∧
      PrimePrefix (scan limit cursor product) finalCursor ∧
        limit < scan limit cursor product * finalCursor := by
  by_cases active : product.val * cursor ≤ limit
  · have nextBound : (nextProduct cursor product).val ≤ limit := by
      rw [nextProduct_value]
      split
      · exact active
      · exact bounded
    have next := scan_spec limit (cursor + 2) (nextProduct cursor product) (by omega)
      (by omega) nextBound (advance_shape cursor product large odd shape)
    rw [scan, dif_pos active]
    exact next
  · rw [scan, dif_neg active]
    exact ⟨cursor, product.property, bounded, shape, by omega⟩
termination_by limit + 2 - cursor
decreasing_by
  have positive := product.property
  have lower : cursor ≤ product.val * cursor := by nlinarith
  omega

theorem optimizedResult_eq (limit : Int) : optimizedResult limit = referenceResult limit := by
  by_cases small : limit < 2
  · have bounded : limit.toNat ≤ 1 := by omega
    have possibilities : limit.toNat = 0 ∨ limit.toNat = 1 := by omega
    rcases possibilities with zero | one
    · simp only [optimizedResult, if_pos small, referenceResult, zero, bestUpTo_zero]
    · simp only [optimizedResult, if_pos small, referenceResult, one, bestUpTo_one]
  · have enough : 2 ≤ limit.toNat := by omega
    obtain ⟨cursor, positive, bounded, shape, stopped⟩ :=
      scan_spec limit.toNat 3 ⟨2, by decide⟩ (by decide) (by decide) enough initial_shape
    rw [optimizedResult, if_neg small]
    exact prefix_eq_maximum limit.toNat _ cursor (bestUpTo limit.toNat)
      positive bounded shape stopped
      (bestUpTo_maximum limit.toNat (by omega))

end ProjectEulerStatements.TotientMaximum
