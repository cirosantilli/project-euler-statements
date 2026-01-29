import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P91

def isRight (a b c d : Nat) : Bool :=
  let dx := if c ≥ a then c - a else a - c
  let dy := if d ≥ b then d - b else b - d
  let dot1 := a * a + b * b
  let dot2 := dx * dx + dy * dy
  let dot3 := c * c + d * d
  decide (dot1 + dot2 = dot3 ∨ dot1 + dot3 = dot2 ∨ dot2 + dot3 = dot1)

def countTriangles (limit : Nat) : Nat :=
  (List.range (limit + 1)).foldl (fun acc x1 =>
    (List.range (limit + 1)).foldl (fun acc2 y1 =>
      (List.range (limit + 1)).foldl (fun acc3 x2 =>
        (List.range (limit + 1)).foldl (fun acc4 y2 =>
          if x1 = 0 ∧ y1 = 0 then acc4
          else if x2 = 0 ∧ y2 = 0 then acc4
          else if x1 = x2 ∧ y1 = y2 then acc4
          else if isRight x1 y1 x2 y2 then acc4 + 1 else acc4) acc3) acc2) acc) 0

def naive (limit : Nat) : Nat :=
  countTriangles limit / 2

example : naive 2 = 14 := by
  native_decide

end ProjectEulerStatements.P91
