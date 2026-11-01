import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P82

def getCol (matrix : List (List Int)) (column : Nat) : List Int :=
  matrix.map (fun row => row.getD column 0)

def addLists (left right : List Int) : List Int :=
  if left.length = right.length then List.zipWith (· + ·) left right else []

def relaxTail (previous : Int) : List Int → List Int → List Int
  | cost :: costs, value :: values =>
      let current := min cost (previous + value)
      current :: relaxTail current costs values
  | _, _ => []

def relaxDown (cost column : List Int) : List Int :=
  if cost.length = column.length then
    match cost, column with
    | first :: costs, _ :: values => first :: relaxTail first costs values
    | _, _ => []
  else []

def relaxUp (cost column : List Int) : List Int :=
  (relaxDown cost.reverse column.reverse).reverse

def columnStep (previous column : List Int) : List Int :=
  relaxUp (relaxDown (addLists previous column) column) column

def minimum : List Int → Int
  | [] => 0
  | first :: rest => rest.foldl min first

def minPath (matrix : List (List Int)) : Int :=
  let columns := (List.range (matrix.headD []).length).map (getCol matrix)
  match columns with
  | [] => 0
  | first :: rest => minimum (rest.foldl columnStep first)

def naive (matrix : List (List Int)) : Int := minPath matrix

end ProjectEulerStatements.P82
