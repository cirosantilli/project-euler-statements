import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P88

def sumUnique (l : List Nat) : Nat :=
  l.eraseDups.foldl (· + ·) 0

def naive (mins : List Nat) : Nat :=
  sumUnique mins

example : sumUnique [4, 6, 8, 12] = 30 := by
  native_decide

example : sumUnique [4, 6, 8, 12, 15, 16] = 61 := by
  native_decide

end ProjectEulerStatements.P88
