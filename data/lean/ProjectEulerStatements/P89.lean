import Mathlib.Data.List.Basic

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
  let rec go (n : Nat) (tbl : List (Nat × List Char)) (fuel : Nat) : List Char :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
        match tbl with
        | [] => []
        | (v, cs) :: tl =>
            if n ≥ v then cs ++ go (n - v) tbl fuel else go n tl fuel
  go n table (n + 1)

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
