import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace ProjectEulerStatements.P93

def evalOps (a b : Int) : List Int :=
  [a + b, a - b, b - a, a * b] ++
  (if b = 0 then [] else [a / b]) ++ (if a = 0 then [] else [b / a])

def concatMap {α β : Type} (f : α → List β) (l : List α) : List β :=
  l.foldr (fun x acc => f x ++ acc) []

def allResults (nums : List Int) : List Int :=
  match nums with
  | [] => []
  | [a] => [a]
  | a :: b :: tl =>
      let combs := evalOps a b
      concatMap (fun v => allResults (v :: tl)) combs
termination_by nums.length
decreasing_by
  all_goals
    simp

def positiveInts (l : List Int) : List Nat :=
  l.foldl (fun acc x => if x > 0 then (Int.toNat x) :: acc else acc) []

def consecutiveCount (l : List Nat) : Nat :=
  let s := l.eraseDups
  let rec go (n steps : Nat) : Nat :=
    match steps with
    | 0 => n - 1
    | steps + 1 =>
        if s.contains n then go (n + 1) steps else n - 1
  go 1 (s.length + 2)

def consecutiveForDigits (digits : List Nat) : Nat :=
  let ints := digits.map (fun d => (d : Int))
  let results := concatMap (fun p => allResults p) ints.permutations
  consecutiveCount (positiveInts results)

partial def combinations (k : Nat) (xs : List Nat) : List (List Nat) :=
  if k == 0 then
    [[]]
  else
    match xs with
    | [] => []
    | x :: xs =>
        let withX := (combinations (k - 1) xs).map (fun ys => x :: ys)
        let withoutX := combinations k xs
        withX ++ withoutX

def digitsToNat (digits : List Nat) : Nat :=
  digits.foldl (fun acc d => acc * 10 + d) 0

partial def bestArithmeticDigits : Nat :=
  let rec loop (sets : List (List Nat)) (bestLen : Nat) (bestDigits : List Nat) : Nat :=
    match sets with
    | [] => digitsToNat bestDigits
    | digits :: rest =>
        let len := consecutiveForDigits digits
        if len > bestLen then
          loop rest len digits
        else
          loop rest bestLen bestDigits
  loop (combinations 4 (List.range 10)) 0 []

def naive : Nat :=
  bestArithmeticDigits

example : consecutiveForDigits [1,2,3,4] = 28 := by
  native_decide

end ProjectEulerStatements.P93
