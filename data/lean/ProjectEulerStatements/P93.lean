import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P93

def evalOps (a b : Int) : List Int :=
  [a + b, a - b, b - a, a * b] ++
  (if b = 0 then [] else [a / b]) ++ (if a = 0 then [] else [b / a])

def concatMap {α β : Type} (f : α → List β) (l : List α) : List β :=
  l.foldr (fun x acc => f x ++ acc) []

def allResultsFuel (nums : List Int) (fuel : Nat) : List Int :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      match nums with
      | [] => []
      | [a] => [a]
      | a :: b :: tl =>
          let combs := evalOps a b
          concatMap (fun v => allResultsFuel (v :: tl) fuel) combs

def allResults (nums : List Int) : List Int :=
  allResultsFuel nums (nums.length * nums.length + 1)

def positiveInts (l : List Int) : List Nat :=
  l.foldl (fun acc x => if x > 0 then (Int.toNat x) :: acc else acc) []

def consecutiveCount (l : List Nat) : Nat :=
  let s := l.eraseDups
  let rec go (n fuel : Nat) : Nat :=
    match fuel with
    | 0 => n - 1
    | fuel + 1 =>
        if s.contains n then go (n + 1) fuel else n - 1
  go 1 (s.length + 2)

def naive (digits : List Nat) : Nat :=
  let ints := digits.map (fun d => (d : Int))
  let results := concatMap (fun p => allResults p) ints.permutations
  consecutiveCount (positiveInts results)

example : naive [1,2,3,4] = 28 := by
  native_decide

end ProjectEulerStatements.P93
