import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P96

def rowOK (row : List Nat) : Bool :=
  let vals := row.filter (fun x => x ≠ 0)
  vals.eraseDups.length = vals.length

def gridOK (g : List (List Nat)) : Bool :=
  g.all rowOK

def naive (grids : List (List (List Nat))) : Nat :=
  grids.length

example : rowOK [1,2,3,4,5,6,7,8,9] = true := by
  native_decide

end ProjectEulerStatements.P96
