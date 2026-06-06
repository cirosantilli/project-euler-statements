import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

namespace ProjectEulerStatements.P9

def tripletProducts (n : Nat) : Finset Nat :=
  (((Finset.Icc 1 n).product (Finset.Icc 1 n)).filter (fun p =>
    let a := p.1
    let b := p.2
    let c := n - a - b
    a < b ∧ b < c ∧ a ^ 2 + b ^ 2 = c ^ 2
  )).image (fun p =>
    let a := p.1
    let b := p.2
    let c := n - a - b
    a * b * c)

/-- Return the largest (a * b * c) where a, b and c are the largest
- Pytagorean triplet such that a + b + c = n. If no such Pytagorean triplets
- exist, return 0.
-
- It is known that there are input values for which multiple triplets exist:
-
- 35 + 84 + 91 = 210 product = 267540
- 60 + 63 + 87 = 210 product = 328860
-/
def naive (n : Nat) : Nat :=
  if h : (tripletProducts n).Nonempty then
    (tripletProducts n).max' h
  else
    0

example : (3 ^ 2 + 4 ^ 2 = (5 : Nat) ^ 2) := by
  native_decide

example : naive 210 = 328860 := by
  native_decide

end ProjectEulerStatements.P9
