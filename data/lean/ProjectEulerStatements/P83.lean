import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P83

def getD2 (matrix : List (List Int)) (r c : Int) : Int :=
  if 0 ≤ r ∧ 0 ≤ c then (matrix.getD r.toNat []).getD c.toNat 0 else 0

def dims (matrix : List (List Int)) : Nat × Nat :=
  (matrix.length, (matrix.headD []).length)

def bigVal (matrix : List (List Int)) : Int :=
  matrix.foldl (fun acc row => acc + row.foldl (· + ·) 0) 0 + 1

def initDist (matrix : List (List Int)) : List (List Int) :=
  let (rows, cols) := dims matrix
  let big := bigVal matrix
  (List.range rows).map (fun (r : Nat) =>
    (List.range cols).map (fun (c : Nat) =>
      if r = 0 ∧ c = 0 then getD2 matrix 0 0 else big))

def neighbors (r c : Int) (rows cols : Nat) : List (Int × Int) :=
  [(r + 1, c), (r, c + 1), (r, c - 1), (r - 1, c)].filter (fun p =>
    decide (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 < rows ∧ p.2 < cols))

def relaxStep (matrix dist : List (List Int)) : List (List Int) :=
  let (rows, cols) := dims matrix
  (List.range rows).map (fun (r : Nat) =>
    (List.range cols).map (fun (c : Nat) =>
      let cur := getD2 dist r c
      let minNb := (neighbors r c rows cols).foldl (fun acc p => min acc (getD2 dist p.1 p.2)) cur
      min cur (getD2 matrix r c + minNb)))

def iterate (matrix dist : List (List Int)) : List (List Int) :=
  let (rows, cols) := dims matrix
  (List.range (rows * cols)).foldl (fun current _ => relaxStep matrix current) dist

def minPath (matrix : List (List Int)) : Int :=
  let (rows, cols) := dims matrix
  getD2 (iterate matrix (initDist matrix)) ((rows : Int) - 1) ((cols : Int) - 1)

def naive (matrix : List (List Int)) : Int := minPath matrix

end ProjectEulerStatements.P83
