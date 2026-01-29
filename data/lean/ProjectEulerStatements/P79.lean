import Mathlib.Data.List.Basic

namespace ProjectEulerStatements.P79

def edgesFrom (s : String) : List (Char × Char) :=
  match s.data with
  | a :: b :: c :: _ => [(a, b), (b, c), (a, c)]
  | _ => []

def concatMap {α β : Type} (f : α → List β) (l : List α) : List β :=
  l.foldr (fun x acc => f x ++ acc) []

def nodes (attempts : List String) : List Char :=
  (concatMap (fun s => s.data) attempts).eraseDups

def edges (attempts : List String) : List (Char × Char) :=
  (concatMap edgesFrom attempts).eraseDups

def removeNode (n : Char) (es : List (Char × Char)) : List (Char × Char) :=
  es.filter (fun e => e.1 ≠ n ∧ e.2 ≠ n)

def incoming (n : Char) (es : List (Char × Char)) : Bool :=
  es.any (fun e => e.2 = n)

def topo (ns : List Char) (es : List (Char × Char)) (fuel : Nat) : List Char :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      match ns.find? (fun n => !incoming n es) with
      | none => []
      | some n =>
          let ns' := ns.erase n
          let es' := removeNode n es
          n :: topo ns' es' fuel

def naive (attempts : List String) : List Char :=
  let ns := nodes attempts
  let es := edges attempts
  topo ns es (ns.length + 1)

end ProjectEulerStatements.P79
