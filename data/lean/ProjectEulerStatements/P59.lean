import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bitwise

namespace ProjectEulerStatements.P59

/-- XOR two bytes. -/
def xor (a b : Nat) : Nat :=
  Nat.xor a b

/-- Decrypt a cipher text with a repeating key. -/
def decrypt (cipher key : List Nat) : List Nat :=
  let rec go (cs : List Nat) (i : Nat) : List Nat :=
    match cs with
    | [] => []
    | c :: cs' =>
        let k := key.getD (i % key.length) 0
        xor c k :: go cs' (i + 1)
  go cipher 0

/-- Check whether `pattern` is a contiguous sublist of `text`. -/
def containsSublist (text pattern : List Nat) : Bool :=
  if pattern = [] then true
  else
    (List.range (text.length + 1)).any (fun i =>
      (text.drop i).take pattern.length = pattern)

/-- Simple English heuristic: contains the word "the". -/
def looksEnglish (text : List Nat) : Bool :=
  containsSublist text [116, 104, 101]

/-- All 3-letter lowercase keys. -/
def keys : List (List Nat) :=
  let letters := (List.range 26).map (fun i => i + 97)
  letters.foldr (fun a acc =>
    letters.foldr (fun b acc2 =>
      (letters.map (fun c => [a, b, c])) ++ acc2) acc) []

/-- Sum of ASCII values of decrypted text using the first key that looks English. -/
def naive (cipher : List Nat) : Nat :=
  match keys.find? (fun k => looksEnglish (decrypt cipher k)) with
  | some k => (decrypt cipher k).sum
  | none => 0

end ProjectEulerStatements.P59
