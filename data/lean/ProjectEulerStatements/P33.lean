import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P33

def eraseNth (l : List Nat) (i : Nat) : List Nat :=
  l.take i ++ l.drop (i + 1)

def isCurious (n d : Nat) : Bool :=
  let dn := Nat.digits 10 n
  let dd := Nat.digits 10 d
  if dn.length = dd.length ∧ 2 ≤ dn.length ∧ n < d then
    let idxN := List.range dn.length
    let idxD := List.range dd.length
    let checks : List (Nat × Nat) :=
      idxN.foldr (fun i acc => (idxD.map fun j => (i, j)) ++ acc) []
    checks.any (fun p =>
      let i := p.1
      let j := p.2
      match dn[i]?, dd[j]? with
      | some x, some y =>
          if x = y ∧ x ≠ 0 then
            let n' := Nat.ofDigits 10 (eraseNth dn i)
            let d' := Nat.ofDigits 10 (eraseNth dd j)
            decide (n * d' = d * n')
          else
            false
      | _, _ => false)
  else
    false

def curiousFractions : List (Nat × Nat) :=
  (List.range 100).foldr (fun n acc =>
    (List.range 100).foldr (fun d acc2 =>
      if isCurious n d then (n, d) :: acc2 else acc2) acc) []

def productDenomReduced : Nat :=
  let prod :=
    curiousFractions.foldl (fun acc p => (acc.1 * p.1, acc.2 * p.2)) (1, 1)
  let g := Nat.gcd prod.1 prod.2
  prod.2 / g

def naive : Nat :=
  productDenomReduced

example : isCurious 49 98 = true := by
  native_decide

end ProjectEulerStatements.P33
