import Mathlib.Data.List.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ProjectEulerStatements.P99

def enumFrom {α : Type} : Nat -> List α -> List (Nat × α)
  | _, [] => []
  | n, x :: xs => (n, x) :: enumFrom (n + 1) xs

noncomputable def score (p : Nat × Nat) : Real :=
  (p.2 : Real) * Real.log (p.1 : Real)

noncomputable def bestLine (pairs : List (Nat × Nat)) : Nat :=
  let indexed := enumFrom 1 pairs
  let rec go (l : List (Nat × (Nat × Nat))) (bestIdx : Nat) (bestScore : Real) : Nat :=
    match l with
    | [] => bestIdx
    | (i, p) :: tl =>
        let s := score p
        if s > bestScore then go tl i s else go tl bestIdx bestScore
  match indexed with
  | [] => 0
  | (i, p) :: tl => go tl i (score p)

noncomputable def naive (pairs : List (Nat × Nat)) : Nat :=
  bestLine pairs

example : (2 ^ 11 : Nat) < 3 ^ 7 := by
  native_decide

end ProjectEulerStatements.P99
