import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs

namespace ProjectEulerStatements.P68

def numDigits (n : Nat) : Nat :=
  (Nat.digits 10 n).length

def concatNat (a b : Nat) : Nat :=
  a * 10 ^ numDigits b + b

def concatList (l : List Nat) : Nat :=
  l.foldl concatNat 0

def maxString3Gon : Nat :=
  let nums := [1,2,3,4,5,6]
  let perms := nums.permutations
  let strings := perms.foldr (fun p acc =>
    match p with
    | [a,b,c,d,e,f] =>
        let s1 := a + b + c
        let s2 := d + c + e
        let s3 := f + e + b
        if decide (s1 = s2 ∧ s2 = s3 ∧ a ≤ d ∧ a ≤ f) then
          let str := concatList [a,b,c,d,c,e,f,e,b]
          str :: acc
        else acc
    | _ => acc) []
  strings.foldl Nat.max 0

def maxString5Gon : Nat :=
  let nums := [1,2,3,4,5,6,7,8,9,10]
  let perms := nums.permutations
  let strings := perms.foldr (fun p acc =>
    match p with
    | [o1,o2,o3,o4,o5,i1,i2,i3,i4,i5] =>
        let s1 := o1 + i1 + i2
        let s2 := o2 + i2 + i3
        let s3 := o3 + i3 + i4
        let s4 := o4 + i4 + i5
        let s5 := o5 + i5 + i1
        if decide (s1 = s2 ∧ s2 = s3 ∧ s3 = s4 ∧ s4 = s5 ∧
            o1 ≤ o2 ∧ o1 ≤ o3 ∧ o1 ≤ o4 ∧ o1 ≤ o5) then
          let str := concatList [o1,i1,i2,o2,i2,i3,o3,i3,i4,o4,i4,i5,o5,i5,i1]
          if numDigits str = 16 then str :: acc else acc
        else acc
    | _ => acc) []
  strings.foldl Nat.max 0

def naive : Nat :=
  maxString5Gon

example : maxString3Gon = 432621513 := by
  native_decide

end ProjectEulerStatements.P68
