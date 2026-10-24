import ProjectEulerStatements.Lib.PellSearch

namespace ProjectEulerStatements.P66

def isSquare (n : Nat) : Bool :=
  let r := Nat.sqrt n
  r * r = n

def minimalX (d : Nat) : Nat :=
  PellMinimum.minimum d

def bestD (limit : Nat) : Nat :=
  PellSearch.answer limit

def naive (limit : Nat) : Nat :=
  bestD limit

theorem minimalX_positive (d : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d) :
    1 < minimalX d := PellMinimum.minimum_positive d nonsquare

theorem minimalX_le (d x y : Nat) (nonsquare : Nat.sqrt d * Nat.sqrt d ≠ d)
    (positive : 1 ≤ y) (solution : x * x = d * y * y + 1) : minimalX d ≤ x :=
  PellMinimum.minimum_le d x y nonsquare positive solution

end ProjectEulerStatements.P66
