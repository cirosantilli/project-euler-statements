import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P11

def gridVal (grid : List (List Nat)) (r c : Nat) : Nat :=
  (grid.getD r []).getD c 0

def prodRight (grid : List (List Nat)) (r c : Nat) : Nat :=
  gridVal grid r c * gridVal grid r (c + 1) * gridVal grid r (c + 2) * gridVal grid r (c + 3)

def prodDown (grid : List (List Nat)) (r c : Nat) : Nat :=
  gridVal grid r c * gridVal grid (r + 1) c * gridVal grid (r + 2) c * gridVal grid (r + 3) c

def prodDiagRight (grid : List (List Nat)) (r c : Nat) : Nat :=
  gridVal grid r c * gridVal grid (r + 1) (c + 1) *
    gridVal grid (r + 2) (c + 2) * gridVal grid (r + 3) (c + 3)

def prodDiagLeft (grid : List (List Nat)) (r c : Nat) : Nat :=
  gridVal grid r c * gridVal grid (r + 1) (c - 1) *
    gridVal grid (r + 2) (c - 2) * gridVal grid (r + 3) (c - 3)

def listMax (l : List Nat) : Nat :=
  l.foldl Nat.max 0

def concatMap {α β : Type} (f : α → List β) (l : List α) : List β :=
  l.foldr (fun x acc => f x ++ acc) []

def productsRight (grid : List (List Nat)) : List Nat :=
  concatMap (fun r => (List.range 17).map (fun c => prodRight grid r c)) (List.range 20)

def productsDown (grid : List (List Nat)) : List Nat :=
  concatMap (fun r => (List.range 20).map (fun c => prodDown grid r c)) (List.range 17)

def productsDiagRight (grid : List (List Nat)) : List Nat :=
  concatMap (fun r => (List.range 17).map (fun c => prodDiagRight grid r c)) (List.range 17)

def productsDiagLeft (grid : List (List Nat)) : List Nat :=
  concatMap (fun r => (List.range 17).map (fun c => prodDiagLeft grid r (c + 3))) (List.range 17)

def naive (grid : List (List Nat)) : Nat :=
  listMax (productsRight grid ++ productsDown grid ++ productsDiagRight grid ++
    productsDiagLeft grid)

example : 26 * 63 * 78 * 14 = 1788696 := by
  native_decide

end ProjectEulerStatements.P11
