import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P67

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

def naive (tri : List (List Nat)) : Nat :=
  maxPath tri

def smallTriangle : List (List Nat) :=
  [ [3], [7, 4], [2, 4, 6], [8, 5, 9, 3] ]

example : maxPath smallTriangle = 23 := by
  native_decide

end ProjectEulerStatements.P67
