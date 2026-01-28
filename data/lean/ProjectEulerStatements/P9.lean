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

def naive (n : Nat) : Nat :=
  if h : (tripletProducts n).Nonempty then
    (tripletProducts n).max' h
  else
    0

example : (3 ^ 2 + 4 ^ 2 = (5 : Nat) ^ 2) := by
  native_decide

end ProjectEulerStatements.P9
