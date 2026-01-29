import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Sort

namespace ProjectEulerStatements.P98

def digitsSorted (n : Nat) : List Nat :=
  (Nat.digits 10 n).mergeSort (fun a b => decide (a ≤ b))

def anagrams (words : List String) : List (String × String) :=
  let rec go (ws : List String) : List (String × String) :=
    match ws with
    | [] => []
    | w :: tl =>
        let wkey := w.data.mergeSort (fun a b => decide (a ≤ b))
        let pairs := tl.filter (fun u => w ≠ u &&
          wkey = u.data.mergeSort (fun a b => decide (a ≤ b)))
        (pairs.map (fun u => (w, u))) ++ go tl
  go words

def naive (words : List String) : Nat :=
  let pairs := anagrams words
  pairs.length

example : digitsSorted 1296 = digitsSorted 9216 := by
  native_decide

end ProjectEulerStatements.P98
