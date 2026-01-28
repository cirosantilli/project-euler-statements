import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P17

def smallWordLen : Nat -> Nat
  | 0 => 0
  | 1 => 3
  | 2 => 3
  | 3 => 5
  | 4 => 4
  | 5 => 4
  | 6 => 3
  | 7 => 5
  | 8 => 5
  | 9 => 4
  | 10 => 3
  | 11 => 6
  | 12 => 6
  | 13 => 8
  | 14 => 8
  | 15 => 7
  | 16 => 7
  | 17 => 9
  | 18 => 8
  | 19 => 8
  | _ => 0

def tensWordLen : Nat -> Nat
  | 2 => 6
  | 3 => 6
  | 4 => 5
  | 5 => 5
  | 6 => 5
  | 7 => 7
  | 8 => 6
  | 9 => 6
  | _ => 0

def wordLen (n : Nat) : Nat :=
  if n = 0 then
    0
  else if n < 20 then
    smallWordLen n
  else if n < 100 then
    tensWordLen (n / 10) + smallWordLen (n % 10)
  else if n < 1000 then
    let h := n / 100
    let r := n % 100
    smallWordLen h + 7 + (if r = 0 then 0 else 3 + wordLen r)
  else if n = 1000 then
    3 + 8
  else
    0

def naive (n : Nat) : Nat :=
  (List.range (n + 1)).foldl (fun acc i => acc + wordLen i) 0

example : naive 5 = 19 := by
  native_decide

example : wordLen 342 = 23 := by
  native_decide

example : wordLen 115 = 20 := by
  native_decide

end ProjectEulerStatements.P17
