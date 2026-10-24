import ProjectEulerStatements.Lib.PellMinimum

/-! Ascending, first-on-tie maximization of the least positive Pell solution. -/
namespace ProjectEulerStatements.PellSearch
set_option Elab.async false

def update (best : Nat × Nat) (d : Nat) : Nat × Nat :=
  if best.2 < PellMinimum.minimum d then (d, PellMinimum.minimum d) else best

def scan (first size bestD bestX : Nat) : Nat × Nat :=
  (List.range' first size).foldl update (bestD, bestX)

def answer (limit : Int) : Nat := (scan 2 (limit - 1).toNat 0 0).1

theorem scan_zero (first bestD bestX : Nat) : scan first 0 bestD bestX = (bestD, bestX) := rfl

theorem scan_succ (first size bestD bestX : Nat) :
    scan first (size + 1) bestD bestX =
      if bestX < PellMinimum.minimum first then
        scan (first + 1) size first (PellMinimum.minimum first)
      else scan (first + 1) size bestD bestX := by
  simp only [scan, List.range'_succ, List.foldl_cons, update]
  split_ifs <;> rfl

end ProjectEulerStatements.PellSearch
