import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P28

def layerSum (k : Nat) : Nat :=
  16 * k^2 + 4 * k + 4

def spiralDiagSum (n : Nat) : Nat :=
  let layers := (n - 1) / 2
  (List.range (layers + 1)).foldl (fun acc k => if k = 0 then acc + 1 else acc + layerSum k) 0

def naive (n : Nat) : Nat :=
  spiralDiagSum n

example : spiralDiagSum 5 = 101 := by
  native_decide

end ProjectEulerStatements.P28
