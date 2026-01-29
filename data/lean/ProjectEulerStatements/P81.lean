import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P81

def getD2 (m : List (List Nat)) (r c : Nat) : Nat :=
  (m.getD r []).getD c 0

def rowStep (prev : List Nat) (row : List Nat) : List Nat :=
  let rec go (prev row : List Nat) (left : Nat) : List Nat :=
    match prev, row with
    | [], [] => []
    | p :: ps, x :: xs =>
        let cur := x + Nat.min p left
        cur :: go ps xs cur
    | _, _ => []
  match prev, row with
  | [], [] => []
  | p :: ps, x :: xs =>
      let first := x + p
      first :: go ps xs first
  | _, _ => []

def minPath (m : List (List Nat)) : Nat :=
  match m with
  | [] => 0
  | r0 :: rs =>
      let init := r0.foldl (fun acc x => acc ++ [x + (acc[acc.length - 1]?).getD 0]) []
      let final := rs.foldl (fun acc row => rowStep acc row) init
      (final[final.length - 1]?).getD 0

def smallMatrix : List (List Nat) :=
  [ [131, 673, 234, 103, 18],
    [201, 96, 342, 965, 150],
    [630, 803, 746, 422, 111],
    [537, 699, 497, 121, 956],
    [805, 732, 524, 37, 331] ]

def naive (m : List (List Nat)) : Nat :=
  minPath m

example : minPath smallMatrix = 2427 := by
  native_decide

end ProjectEulerStatements.P81
