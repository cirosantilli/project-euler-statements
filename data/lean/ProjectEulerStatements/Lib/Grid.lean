import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-! Grid access and segment bounds, independent of any Python representation. -/

namespace ProjectEulerStatements.Grid

inductive Direction where
  | right
  | down
  | downRight
  | downLeft
deriving DecidableEq, Repr

def Direction.row (direction : Direction) (start : Int) (position : Nat) : Int :=
  match direction with
  | .right => start
  | _ => start + position

def Direction.column (direction : Direction) (start : Int) (position : Nat) : Int :=
  match direction with
  | .down => start
  | .downLeft => start - position
  | _ => start + position

/-- Access by signed coordinates, using a supplied value outside the grid. -/
def get (grid : List (List α)) (row column : Int) (default : α) : α :=
  if 0 ≤ row ∧ 0 ≤ column then
    ((grid[row.toNat]?).getD [])[column.toNat]?.getD default
  else default

theorem get_of_negative_row (grid : List (List α)) (row column : Int) (default : α)
    (negative : row < 0) : get grid row column default = default := by
  simp [get, show ¬ 0 ≤ row by omega]

theorem get_of_negative_column (grid : List (List α)) (row column : Int) (default : α)
    (negative : column < 0) : get grid row column default = default := by
  simp [get, show ¬ 0 ≤ column by omega]

theorem get_of_bounds (grid : List (List α)) (row column : Nat) (default : α)
    (rowValid : row < grid.length) (columnValid : column < grid[row].length) :
    get grid row column default = grid[row][column] := by
  simp [get, List.getElem?_eq_getElem rowValid, List.getElem?_eq_getElem columnValid]

theorem get_of_row_outside (grid : List (List α)) (row column : Nat) (default : α)
    (outside : grid.length ≤ row) : get grid row column default = default := by
  simp [get, List.getElem?_eq_none outside]

theorem get_of_column_outside (grid : List (List α)) (row column : Nat) (default : α)
    (rowValid : row < grid.length) (outside : grid[row].length ≤ column) :
    get grid row column default = default := by
  simp [get, List.getElem?_eq_getElem rowValid, List.getElem?_eq_none outside]

/-- Every point between two valid endpoints remains inside the coordinate bounds. -/
theorem segment_bounds (start stride bound : Int) (count position : Nat)
    (first : 0 ≤ start ∧ start < bound)
    (last : 0 ≤ start + ((count : Int) - 1) * stride ∧ start + ((count : Int) - 1) * stride < bound)
    (inside : position < count) :
    0 ≤ start + (position : Int) * stride ∧ start + (position : Int) * stride < bound := by
  have positionNonnegative : (0 : Int) ≤ position := by omega
  have remaining : (0 : Int) ≤ (count : Int) - 1 - position := by omega
  by_cases positive : 0 ≤ stride
  · have lower := mul_nonneg positionNonnegative positive
    have upper := mul_nonneg remaining positive
    constructor <;> nlinarith [first.1, first.2, last.1, last.2]
  · have lower := mul_nonpos_of_nonneg_of_nonpos remaining (by omega : stride ≤ 0)
    have upper := mul_nonpos_of_nonneg_of_nonpos positionNonnegative (by omega : stride ≤ 0)
    constructor <;> nlinarith [first.1, first.2, last.1, last.2]

end ProjectEulerStatements.Grid
