import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P81

/-- Accumulate a row once its left-hand boundary value is known. -/
def scanRow (left : Int) : List Int → List Int → List Int
  | p :: ps, x :: xs =>
      let value := x + min p left
      value :: scanRow value ps xs
  | _, _ => []

def rowStep : List Int → List Int → List Int
  | p :: ps, x :: xs =>
      let first := x + p
      first :: scanRow first ps xs
  | _, _ => []

def firstRowFrom (left : Int) : List Int → List Int
  | [] => []
  | x :: xs => (left + x) :: firstRowFrom (left + x) xs

def firstRow (row : List Int) : List Int := firstRowFrom 0 row

def minPath : List (List Int) → Int
  | [] => 0
  | row :: rows => ((rows.foldl rowStep (firstRow row)).getLast?).getD 0

def naive (matrix : List (List Int)) : Int := minPath matrix

end ProjectEulerStatements.P81
