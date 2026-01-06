namespace ProjectEulerStatements.P1

--import Mathlib
--/-- The sum of all natural numbers `< max` that are multiples of `3` or `5`. -/
--def pe1def := fun (max : Nat) =>
--  ((Finset.range max).filter (fun n => (3 ∣ n) ∨ (5 ∣ n))).sum (fun n => n)

def naive : Nat -> Nat
  | 0       => 0
  | n + 1   =>
      let s := naive n
      if n % 3 = 0 ∨ n % 5 = 0 then s + n else s
