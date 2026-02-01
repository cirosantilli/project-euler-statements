import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P13

/-- The top `k` digits of the sum of `num` as a number. -/
def naive (nums : List Nat) (k : Nat) : Nat :=
  let ds := (Nat.digits 10 nums.sum).reverse
  Nat.ofDigits 10 (ds.take k).reverse

end ProjectEulerStatements.P13
