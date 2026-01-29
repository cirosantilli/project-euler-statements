import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P82

def getCol (m : List (List Nat)) (c : Nat) : List Nat :=
  m.map (fun row => row.getD c 0)

def addLists : List Nat -> List Nat -> List Nat
  | [], [] => []
  | x :: xs, y :: ys => (x + y) :: addLists xs ys
  | _, _ => []

def relaxDown : List Nat -> List Nat -> List Nat
  | [], [] => []
  | c0 :: cs, _ :: vs =>
      let rec go (prev : Nat) (cs vs : List Nat) : List Nat :=
        match cs, vs with
        | [], [] => []
        | c :: ct, v :: vt =>
            let cur := Nat.min c (prev + v)
            cur :: go cur ct vt
        | _, _ => []
      c0 :: go c0 cs vs
  | _, _ => []

def relaxUp (cost col : List Nat) : List Nat :=
  (relaxDown cost.reverse col.reverse).reverse

def minPath (m : List (List Nat)) : Nat :=
  let cols :=
    match m with
    | [] => []
    | r0 :: _ => (List.range r0.length).map (fun c => getCol m c)
  match cols with
  | [] => 0
  | c0 :: cs =>
      let init := c0
      let final := cs.foldl (fun acc col =>
        let base := addLists acc col
        let down := relaxDown base col
        relaxUp down col) init
      match final with
      | [] => 0
      | x :: xs => xs.foldl Nat.min x

def smallMatrix : List (List Nat) :=
  [ [131, 673, 234, 103, 18],
    [201, 96, 342, 965, 150],
    [630, 803, 746, 422, 111],
    [537, 699, 497, 121, 956],
    [805, 732, 524, 37, 331] ]

def naive (m : List (List Nat)) : Nat :=
  minPath m

example : minPath smallMatrix = 994 := by
  native_decide

end ProjectEulerStatements.P82
