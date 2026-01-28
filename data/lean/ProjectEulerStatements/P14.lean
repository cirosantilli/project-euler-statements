import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax

namespace ProjectEulerStatements.P14

def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def collatzLenBound : Nat -> Nat -> Nat
  | _, 0 => 0
  | n, fuel + 1 =>
      if n = 1 then
        1
      else
        1 + collatzLenBound (collatzStep n) fuel

noncomputable def naive (limit fuel : Nat) : Nat :=
  match List.argmax (fun n => collatzLenBound n fuel) (List.range (limit + 1)) with
  | some n => n
  | none => 0

example : collatzLenBound 13 20 = 10 := by
  native_decide

end ProjectEulerStatements.P14
