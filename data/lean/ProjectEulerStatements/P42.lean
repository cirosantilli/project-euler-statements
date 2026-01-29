import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P42

def wordValue (s : String) : Nat :=
  s.data.foldl (fun acc c => acc + (c.toNat - 'A'.toNat + 1)) 0

def isTriangle (n : Nat) : Bool :=
  (List.range (n + 1)).any (fun k => k * (k + 1) / 2 = n)

def countTriangleWords (words : List String) : Nat :=
  words.foldl (fun acc w => if isTriangle (wordValue w) then acc + 1 else acc) 0

def naive (words : List String) : Nat :=
  countTriangleWords words

example : wordValue "SKY" = 55 := by
  native_decide

example : isTriangle 55 = true := by
  native_decide

end ProjectEulerStatements.P42
