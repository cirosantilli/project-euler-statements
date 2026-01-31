import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace ProjectEulerStatements.P89

def value (c : Char) : Nat :=
  if c = 'I' then 1
  else if c = 'V' then 5
  else if c = 'X' then 10
  else if c = 'L' then 50
  else if c = 'C' then 100
  else if c = 'D' then 500
  else if c = 'M' then 1000
  else 0

def romanToInt : List Char -> Nat
  | [] => 0
  | [a] => value a
  | a :: b :: tl =>
      if value a < value b then
        value b - value a + romanToInt tl
      else
        value a + romanToInt (b :: tl)

def intToRomanAux (n : Nat) : List Char :=
  let table : List (Nat × List Char) :=
    [ (1000, ['M']),
      (900, ['C','M']),
      (500, ['D']),
      (400, ['C','D']),
      (100, ['C']),
      (90, ['X','C']),
      (50, ['L']),
      (40, ['X','L']),
      (10, ['X']),
      (9, ['I','X']),
      (5, ['V']),
      (4, ['I','V']),
      (1, ['I']) ]
  let rec go (n : Nat) (tbl : List (Nat × List Char)) : List Char :=
    match tbl with
    | [] => []
    | (v, cs) :: tl =>
        if h0 : v = 0 then
          (by
            have _ := h0
            exact go n tl)
        else if hge : n ≥ v then
          (by
            have _ := hge
            exact cs ++ go (n - v) ((v, cs) :: tl))
        else
          go n tl
  termination_by
    n + match tbl with
    | [] => 0
    | _ :: tl => tl.length + 1
  decreasing_by
    · cases tl <;> simp
    · have hv : 0 < v := Nat.pos_of_ne_zero h0
      have hsub : n - v < n := Nat.sub_lt_of_pos_le hv hge
      exact Nat.add_lt_add_right hsub (tl.length + 1)
    · cases tl <;> simp
  go n table

def minimalRoman (s : String) : String :=
  let n := romanToInt s.data
  String.mk (intToRomanAux n)

def savedChars (s : String) : Nat :=
  s.length - (minimalRoman s).length

def naive (list : List String) : Nat :=
  list.foldl (fun acc s => acc + savedChars s) 0

example : romanToInt "XVI".data = 16 := by
  native_decide

end ProjectEulerStatements.P89
