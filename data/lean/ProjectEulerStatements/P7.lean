import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Nth

namespace ProjectEulerStatements.P7

noncomputable def naive (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => Nat.nth Nat.Prime n

def primesUpTo (n : Nat) : Finset Nat :=
  (Finset.range (n + 1)).filter Nat.Prime

example : (primesUpTo 13).card = 6 := by
  native_decide

example : (primesUpTo 13).max' (by native_decide : (primesUpTo 13).Nonempty) = 13 := by
  native_decide

end ProjectEulerStatements.P7
