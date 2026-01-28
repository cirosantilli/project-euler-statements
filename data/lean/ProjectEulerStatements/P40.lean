import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P40

def digitsBE (n : Nat) : List Nat :=
  (Nat.digits 10 n).reverse

def champernowneDigits (limit : Nat) : List Nat :=
  (List.range limit).foldl (fun acc i => acc ++ digitsBE (i + 1)) []
def digitAt (n limit : Nat) : Nat :=
  (champernowneDigits limit).getD (n - 1) 0

def productDigits (positions : List Nat) (limit : Nat) : Nat :=
  positions.foldl (fun acc i => acc * digitAt i limit) 1

def naive (limit : Nat) : Nat :=
  productDigits [1, 10, 100, 1000, 10000, 100000, 1000000] limit

example : digitAt 12 20 = 1 := by
  native_decide

end ProjectEulerStatements.P40
