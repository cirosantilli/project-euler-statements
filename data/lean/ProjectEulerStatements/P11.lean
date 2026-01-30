import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P11

def gridVal (grid : List (List Nat)) (r c : Nat) : Nat :=
  (grid.getD r []).getD c 0

def prodRightN (grid : List (List Nat)) (r c n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc * gridVal grid r (c + i)) 1

def prodDownN (grid : List (List Nat)) (r c n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc * gridVal grid (r + i) c) 1

def prodDiagRightN (grid : List (List Nat)) (r c n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc * gridVal grid (r + i) (c + i)) 1

def prodDiagLeftN (grid : List (List Nat)) (r c n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc * gridVal grid (r + i) (c - i)) 1

def listMax (l : List Nat) : Nat :=
  l.foldl Nat.max 0

def concatMap {α β : Type} (f : α → List β) (l : List α) : List β :=
  l.foldr (fun x acc => f x ++ acc) []

def productsRightN (grid : List (List Nat)) (n : Nat) : List Nat :=
  concatMap (fun r => (List.range (21 - n)).map (fun c => prodRightN grid r c n)) (List.range 20)

def productsDownN (grid : List (List Nat)) (n : Nat) : List Nat :=
  concatMap (fun r => (List.range 20).map (fun c => prodDownN grid r c n)) (List.range (21 - n))

def productsDiagRightN (grid : List (List Nat)) (n : Nat) : List Nat :=
  concatMap (fun r => (List.range (21 - n)).map (fun c => prodDiagRightN grid r c n))
    (List.range (21 - n))

def productsDiagLeftN (grid : List (List Nat)) (n : Nat) : List Nat :=
  concatMap (fun r =>
    (List.range (21 - n)).map (fun c => prodDiagLeftN grid r (c + (n - 1)) n))
    (List.range (21 - n))

/- Find the great product of `n` adjacent numbers in the grid `grid`. -/
def naive (grid : List (List Nat)) (n : Nat) : Nat :=
  listMax (productsRightN grid n ++ productsDownN grid n ++ productsDiagRightN grid n ++
    productsDiagLeftN grid n)

end ProjectEulerStatements.P11
