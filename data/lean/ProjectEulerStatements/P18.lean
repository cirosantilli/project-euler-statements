import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace ProjectEulerStatements.P18

def Triangle (n : Nat) :=
  { rows : List (List Nat) //
      rows.length = n ∧
        ∀ i (hi : i < rows.length), (rows.get ⟨i, hi⟩).length = i + 1 }

def maxRow : List Nat -> List Nat -> List Nat
  | [], _ => []
  | _ :: _, [] => []
  | x :: xs, y :: z :: zs => (x + Nat.max y z) :: maxRow xs (z :: zs)
  | _, _ => []

def maxPath (tri : List (List Nat)) : Nat :=
  match tri.reverse with
  | [] => 0
  | r :: rs =>
      List.getD (List.foldl (fun acc row => maxRow row acc) r rs) 0 0

def smallTriangleT : Triangle 4 := by
  refine ⟨
    ([
        [3],
        [7, 4],
        [2, 4, 6],
        [8, 5, 9, 3]
      ] : List (List Nat)
    ),
    ?_
  ⟩
  decide

/-- Maxium path down a Triangle `tri` going left or right. -/
def naive (tri : Triangle n) : Nat :=
  maxPath tri.1

example : maxPath smallTriangleT.1 = 23 := by
  native_decide

end ProjectEulerStatements.P18
