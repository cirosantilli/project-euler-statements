import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P90

def squares : List (Nat × Nat) :=
  [ (0,1), (0,4), (0,9), (1,6), (2,5), (3,6), (4,9), (6,4), (8,1) ]

def expand69 (l : List Nat) : List Nat :=
  if l.contains 6 || l.contains 9 then
    (l ++ [6, 9]).eraseDups
  else l

def canShow (a b : List Nat) : Bool :=
  let a' := expand69 a
  let b' := expand69 b
  squares.all (fun p =>
    (a'.contains p.1 && b'.contains p.2) || (a'.contains p.2 && b'.contains p.1))

def choose6 : List Nat -> List (List Nat)
  | l =>
      let rec go (l : List Nat) (k : Nat) : List (List Nat) :=
        match k, l with
        | 0, _ => [[]]
        | _, [] => []
        | k + 1, x :: xs =>
            let withX := (go xs k).map (fun t => x :: t)
            let withoutX := go xs (k + 1)
            withX ++ withoutX
      go l 6

def enumFrom {α : Type} : Nat -> List α -> List (Nat × α)
  | _, [] => []
  | n, x :: xs => (n, x) :: enumFrom (n + 1) xs

def countArrangements : Nat :=
  let cubes := choose6 (List.range 10)
  let pairs :=
    (enumFrom 0 cubes).foldl (fun acc p =>
      let i := p.1
      let a := p.2
      let rest := (cubes.drop i)
      acc + (rest.filter (fun b => canShow a b)).length) 0
  pairs

def naive : Nat :=
  countArrangements

example : canShow [0,5,6,7,8,9] [1,2,3,4,8,9] = true := by
  native_decide

end ProjectEulerStatements.P90
