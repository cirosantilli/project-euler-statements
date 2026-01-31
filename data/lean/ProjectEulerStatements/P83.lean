import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P83

def getD2 (m : List (List Nat)) (r c : Nat) : Nat :=
  (m.getD r []).getD c 0

def dims (m : List (List Nat)) : Nat × Nat :=
  match m with
  | [] => (0, 0)
  | r :: _ => (m.length, r.length)

def bigVal (m : List (List Nat)) : Nat :=
  m.foldl (fun acc row => acc + row.foldl (· + ·) 0) 0 + 1

def initDist (m : List (List Nat)) : List (List Nat) :=
  let (rows, cols) := dims m
  let big := bigVal m
  (List.range rows).map (fun r =>
    (List.range cols).map (fun c =>
      if r = 0 ∧ c = 0 then getD2 m 0 0 else big))

def neighbors (r c rows cols : Nat) : List (Nat × Nat) :=
  [ (r + 1, c), (r, c + 1), (r, c - 1), (r - 1, c) ].filter (fun p =>
      let rr := p.1
      let cc := p.2
      decide (rr < rows ∧ cc < cols))

def relaxStep (m dist : List (List Nat)) : List (List Nat) :=
  let (rows, cols) := dims m
  (List.range rows).map (fun r =>
    (List.range cols).map (fun c =>
      let cur := getD2 dist r c
      let nb := neighbors r c rows cols
      let minNb := nb.foldl (fun acc p => Nat.min acc (getD2 dist p.1 p.2)) cur
      Nat.min cur (getD2 m r c + minNb)))

def iterate (m dist : List (List Nat)) : List (List Nat) :=
  let rec go (dist : List (List Nat)) (steps : Nat) : List (List Nat) :=
    match steps with
    | 0 => dist
    | steps + 1 =>
        let dist' := relaxStep m dist
        go dist' steps
  let (rows, cols) := dims m
  go dist (rows * cols)

def minPath (m : List (List Nat)) : Nat :=
  let dist0 := initDist m
  let dist := iterate m dist0
  let (rows, cols) := dims m
  getD2 dist (rows - 1) (cols - 1)

def smallMatrix : List (List Nat) :=
  [ [131, 673, 234, 103, 18],
    [201, 96, 342, 965, 150],
    [630, 803, 746, 422, 111],
    [537, 699, 497, 121, 956],
    [805, 732, 524, 37, 331] ]

def naive (m : List (List Nat)) : Nat :=
  minPath m

example : minPath smallMatrix = 2297 := by
  native_decide

end ProjectEulerStatements.P83
