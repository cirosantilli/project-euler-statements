import Mathlib.Data.List.Basic
import ProjectEulerStatements.Lib.GridProducts

/-! Reference grid products and equivalence of the candidate enumeration orders. -/

namespace ProjectEulerStatements.P11

def gridVal (grid : List (List Nat)) (r c : Nat) : Nat :=
  (grid.getD r []).getD c 0

theorem gridVal_eq_get (grid : List (List Nat)) (r c : Nat) :
    gridVal grid r c = Grid.get grid r c 0 := by
  simp [gridVal, Grid.get, List.getD_eq_getElem?_getD]

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

/-- The greatest product of `n` adjacent numbers in the grid `grid`. -/
def naive (grid : List (List Nat)) (n : Nat) : Nat :=
  listMax (productsRightN grid n ++ productsDownN grid n ++ productsDiagRightN grid n ++
    productsDiagLeftN grid n)

theorem prodRightN_eq_segmentProduct (grid : List (List Nat)) (r c n : Nat) :
    prodRightN grid r c n = Grid.segmentProduct grid .right r c n := by
  simp [prodRightN, Grid.segmentProduct, gridVal_eq_get, Grid.Direction.row,
    Grid.Direction.column, Nat.cast_add]

theorem prodDownN_eq_segmentProduct (grid : List (List Nat)) (r c n : Nat) :
    prodDownN grid r c n = Grid.segmentProduct grid .down r c n := by
  simp [prodDownN, Grid.segmentProduct, gridVal_eq_get, Grid.Direction.row,
    Grid.Direction.column, Nat.cast_add]

theorem prodDiagRightN_eq_segmentProduct (grid : List (List Nat)) (r c n : Nat) :
    prodDiagRightN grid r c n = Grid.segmentProduct grid .downRight r c n := by
  simp [prodDiagRightN, Grid.segmentProduct, gridVal_eq_get, Grid.Direction.row,
    Grid.Direction.column, Nat.cast_add]

theorem prodDiagLeftN_eq_segmentProduct (grid : List (List Nat)) (r c n : Nat)
    (enough : n - 1 ≤ c) :
    prodDiagLeftN grid r c n = Grid.segmentProduct grid .downLeft r c n := by
  have reads : (List.range n).map (fun i => gridVal grid (r + i) (c - i)) =
      (List.range n).map (fun i => Grid.get grid
        (Grid.Direction.downLeft.row r i) (Grid.Direction.downLeft.column c i) 0) := by
    apply List.map_congr_left
    intro i member
    have inside : i < n := List.mem_range.mp member
    have column : i ≤ c := by omega
    simp [gridVal_eq_get, Grid.Direction.row, Grid.Direction.column,
      Nat.cast_add, Nat.cast_sub column]
  have folded := congrArg (fun values : List Nat => values.foldl (· * ·) 1) reads
  simpa only [List.foldl_map] using folded

theorem concatMap_eq_flatMap {α β : Type} (f : α → List β) (items : List α) :
    concatMap f items = items.flatMap f := by
  induction items with
  | nil => rfl
  | cons value rest ih => simpa [concatMap] using congrArg (f value ++ ·) ih

/-- The reference's four lists are the direction-based enumeration on a 20×20 rectangle. -/
theorem naive_eq_directional (grid : List (List Nat)) (n : Nat) :
    naive grid n = (Grid.directionalProducts grid 20 20 n).foldl max 0 := by
  have left (r c : Nat) : prodDiagLeftN grid r (c + (n - 1)) n =
      Grid.segmentProduct grid .downLeft r (c + (n - 1)) n :=
    prodDiagLeftN_eq_segmentProduct grid r (c + (n - 1)) n (Nat.le_add_left _ _)
  simp [naive, listMax, productsRightN, productsDownN, productsDiagRightN,
    productsDiagLeftN, concatMap_eq_flatMap, Grid.directionalProducts, Grid.directions,
    Grid.starts, List.map_flatMap, List.map_map, Function.comp_def,
    prodRightN_eq_segmentProduct, prodDownN_eq_segmentProduct,
    prodDiagRightN_eq_segmentProduct, left, List.append_assoc]

/-- The optimized search order visits exactly the same positive-length candidates. -/
theorem naive_eq_scanned_pos (grid : List (List Nat)) (n : Nat) (positive : 0 < n) :
    naive grid n = (Grid.scannedProducts grid 20 20 n).foldl max 0 := by
  rw [naive_eq_directional, Grid.maximum_directional_eq_scanned grid 20 20 n positive]

/-- Search-order equivalence includes the empty product convention. -/
theorem naive_eq_scanned (grid : List (List Nat)) (n : Nat) :
    naive grid n = (Grid.scannedProducts grid 20 20 n).foldl max 0 := by
  cases n with
  | zero =>
      rw [naive_eq_directional, Grid.maximum_directional_zero,
        Grid.maximum_scanned_zero grid 20 20 (by decide) (by decide)]
  | succ n => exact naive_eq_scanned_pos grid (n + 1) (by omega)

end ProjectEulerStatements.P11
