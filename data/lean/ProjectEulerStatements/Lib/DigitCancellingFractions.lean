import ProjectEulerStatements.P33
import Mathlib.Data.List.Range

/-! Source-oriented searches and products for the digit-cancelling fractions. -/
namespace ProjectEulerStatements.DigitCancellingFractions

set_option Elab.async false

/-- The four fractions, in the numerator/denominator search order. -/
def fractions : List (Nat × Nat) := [(16, 64), (19, 95), (26, 65), (49, 98)]

/-- The product before cancellation, retaining both integer accumulators. -/
def product (items : List (Nat × Nat)) : Nat × Nat :=
  items.foldl (fun acc item => (acc.1 * item.1, acc.2 * item.2)) (1, 1)

/-- The source divides the denominator product by the greatest common divisor. -/
def denominator (items : List (Nat × Nat)) : Nat :=
  let multiplied := product items
  multiplied.2 / Nat.gcd multiplied.1 multiplied.2

/-- One complete denominator row of the reference search. -/
def referenceRow (n : Nat) : List (Nat × Nat) :=
  ((List.range 100).filter (P33.isCurious n)).map (fun d => (n, d))

/-- Membership of a digit in a two-digit decimal representation. -/
def hasDigit (n digit : Nat) : Prop := n / 10 = digit ∨ n % 10 = digit

instance (n digit : Nat) : Decidable (hasDigit n digit) := inferInstanceAs (Decidable (_ ∨ _))

/-- Removing the first occurrence scans the tens digit before the units digit. -/
def remainder (n digit : Nat) : Nat := if n / 10 = digit then n % 10 else n / 10

/-- One cancellation attempt in the optimized source's nonzero-digit loop. -/
def cancellation (n d digit : Nat) : Bool :=
  decide (hasDigit n digit ∧ hasDigit d digit ∧ remainder d digit ≠ 0 ∧
    n * remainder d digit = d * remainder n digit)

/-- The source skips the trailing-zero case, then tries digits one through nine. -/
def optimizedPredicate (n d : Nat) : Bool :=
  if n % 10 = 0 ∧ d % 10 = 0 then false
  else (List.range' 1 9).any (cancellation n d)

/-- The strict upper triangle searched by the optimized implementation. -/
def optimizedRow (n : Nat) : List (Nat × Nat) :=
  ((List.range' (n + 1) (99 - n)).filter (optimizedPredicate n)).map (fun d => (n, d))

def optimizedFractions : List (Nat × Nat) :=
  (List.range' 10 90).flatMap optimizedRow

private theorem row_fold (n : Nat) (ds : List Nat) (acc : List (Nat × Nat)) :
    ds.foldr (fun d rest => if P33.isCurious n d then (n, d) :: rest else rest) acc =
      (ds.filter (P33.isCurious n)).map (fun d => (n, d)) ++ acc := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      cases accepted : P33.isCurious n d <;> simp [accepted, ih]

/-- The nested reference folds preserve the row-major list order exactly. -/
theorem curiousFractions_eq_rows :
    P33.curiousFractions = (List.range 100).flatMap referenceRow := by
  have enumerate (ns : List Nat) :
      ns.foldr (fun n acc => (List.range 100).foldr
        (fun d rest => if P33.isCurious n d then (n, d) :: rest else rest) acc) [] =
        ns.flatMap referenceRow := by
    induction ns with
    | nil => rfl
    | cons n ns ih =>
        rw [List.foldr_cons, row_fold, ih, List.flatMap_cons]
        rfl
  exact enumerate (List.range 100)

theorem naive_eq_denominator : P33.naive = denominator P33.curiousFractions := by
  unfold P33.naive P33.productDenomReduced denominator product
  generalize P33.curiousFractions = items
  rfl

set_option maxRecDepth 10000 in
/-- Only the small, explicit witness list is reduced here. -/
theorem fractions_denominator : denominator fractions = 100 := by decide +kernel

end ProjectEulerStatements.DigitCancellingFractions
