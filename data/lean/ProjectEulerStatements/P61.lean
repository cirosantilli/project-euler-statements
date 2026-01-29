import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P61

def p3 (n : Nat) : Nat := n * (n + 1) / 2

def p4 (n : Nat) : Nat := n * n

def p5 (n : Nat) : Nat := n * (3 * n - 1) / 2

def p6 (n : Nat) : Nat := n * (2 * n - 1)

def p7 (n : Nat) : Nat := n * (5 * n - 3) / 2

def p8 (n : Nat) : Nat := n * (3 * n - 2)

def lastTwo (n : Nat) : Nat := n % 100

def firstTwo (n : Nat) : Nat := n / 100

def isCyclicPair (a b : Nat) : Bool :=
  lastTwo a = firstTwo b

def isCyclicList : List Nat -> Bool
  | [] => false
  | [_] => false
  | xs =>
      let rec go : List Nat -> Bool
        | [] => true
        | [_] => true
        | a :: b :: tl => if isCyclicPair a b then go (b :: tl) else false
      let hd := xs.headD 0
      let last := xs.getLastD 0
      go xs && isCyclicPair last hd

def fourDigit (f : Nat -> Nat) (limit : Nat) : List Nat :=
  (List.range (limit + 1)).map f |>.filter (fun n => decide (1000 ≤ n ∧ n < 10000))

def naive (limit : Nat) : Nat :=
  let t3 := fourDigit p3 limit
  let t4 := fourDigit p4 limit
  let t5 := fourDigit p5 limit
  let t6 := fourDigit p6 limit
  let t7 := fourDigit p7 limit
  let t8 := fourDigit p8 limit
  let sums :=
    t3.foldr (fun a acc =>
      t4.foldr (fun b acc2 =>
        t5.foldr (fun c acc3 =>
          t6.foldr (fun d acc4 =>
            t7.foldr (fun e acc5 =>
              t8.foldr (fun f acc6 =>
                let xs := [a, b, c, d, e, f]
                if isCyclicList xs then
                  let s := xs.foldl (fun acc' x => acc' + x) 0
                  s :: acc6
                else
                  acc6) acc5) acc4) acc3) acc2) acc) []
  sums.foldl Nat.max 0

example : isCyclicList [8128, 2882, 8281] = true := by
  native_decide

end ProjectEulerStatements.P61
