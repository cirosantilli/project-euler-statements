import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P33

def digits2 (n : Nat) : Nat × Nat :=
  (n / 10, n % 10)

def isCurious (n d : Nat) : Bool :=
  if n ≥ 10 ∧ n < d ∧ d < 100 then
    if n % 10 = 0 ∧ d % 10 = 0 then
      false
    else
      let (a, b) := digits2 n
      let (c, e) := digits2 d
      let checks : List (Nat × Nat) :=
        [ (a, c), (a, e), (b, c), (b, e) ]
      checks.any (fun p =>
        let x := p.1
        let y := p.2
        if x = y ∧ x ≠ 0 then
          let n' := if a = x then b else a
          let d' := if c = y then e else c
          n * d' = d * n'
        else
          false)
  else
    false
def curiousFractions : List (Nat × Nat) :=
  (List.range 100).foldr (fun n acc =>
    (List.range 100).foldr (fun d acc2 =>
      if isCurious n d then (n, d) :: acc2 else acc2) acc) []

def productDenomReduced : Nat :=
  let prod := curiousFractions.foldl (fun acc p => (acc.1 * p.1, acc.2 * p.2)) (1, 1)
  let g := Nat.gcd prod.1 prod.2
  prod.2 / g

def naive : Nat :=
  productDenomReduced

example : isCurious 49 98 = true := by
  native_decide

end ProjectEulerStatements.P33
