import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort

namespace ProjectEulerStatements.P54

inductive Suit
  | H | D | C | S
  deriving DecidableEq

inductive Rank
  | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | J | Q | K | A
  deriving DecidableEq

abbrev Card := Rank × Suit

def rankValue : Rank → Nat
  | .r2 => 2
  | .r3 => 3
  | .r4 => 4
  | .r5 => 5
  | .r6 => 6
  | .r7 => 7
  | .r8 => 8
  | .r9 => 9
  | .r10 => 10
  | .J => 11
  | .Q => 12
  | .K => 13
  | .A => 14

/-- Ranks of a hand, as natural values. -/
def handRanks (hand : List Card) : List Nat :=
  hand.map (fun c => rankValue c.1)

/-- Suits of a hand. -/
def handSuits (hand : List Card) : List Suit :=
  hand.map (fun c => c.2)

/-- All suits equal. -/
def isFlush (hand : List Card) : Bool :=
  match handSuits hand with
  | [] => false
  | s :: ss => ss.all (fun t => t = s)

/-- Sorted ranks in ascending order. -/
def sortedRanks (rs : List Nat) : List Nat :=
  rs.mergeSort (fun a b => decide (a ≤ b))

/-- True if ranks form a straight (Ace can be low in A-2-3-4-5). -/
def isStraight (rs : List Nat) : Bool :=
  let rs := sortedRanks rs
  if rs = [2, 3, 4, 5, 14] then
    true
  else
    match rs with
    | [] => false
    | r0 :: _ =>
        (List.range rs.length).all (fun i =>
          match rs[i]? with
          | some r => r = r0 + i
          | none => false)

/-- Highest card in a straight (wheel counts as 5). -/
def straightHigh (rs : List Nat) : Nat :=
  let rs := sortedRanks rs
  if rs = [2, 3, 4, 5, 14] then 5 else rs.getLastD 0

/-- Frequency pairs `(count, value)` for ranks. -/
def rankCounts (rs : List Nat) : List (Nat × Nat) :=
  let vals := rs.eraseDups
  vals.map (fun v => (rs.count v, v))

/-- Sort counts by count desc, then value desc. -/
def sortCounts (cs : List (Nat × Nat)) : List (Nat × Nat) :=
  cs.mergeSort (fun a b =>
    if a.1 = b.1 then decide (a.2 > b.2) else decide (a.1 > b.1))

/-- Tie-break key from counts (values repeated by their multiplicity). -/
def countsKey (rs : List Nat) : List Nat :=
  (sortCounts (rankCounts rs)).foldr (fun p acc => List.replicate p.1 p.2 ++ acc) []

/-- Hand score: category and tie-break key. Higher category is better. -/
def handScore (hand : List Card) : Nat × List Nat :=
  let rs := handRanks hand
  let flush := isFlush hand
  let straight := isStraight rs
  let sorted := sortedRanks rs
  let keyCounts := countsKey rs
  if straight && flush then
    if sorted = [10, 11, 12, 13, 14] then (9, []) else (8, [straightHigh rs])
  else
    match sortCounts (rankCounts rs) with
    | (4, _) :: _ => (7, keyCounts)
    | (3, _) :: (2, _) :: _ => (6, keyCounts)
    | _ =>
        if flush then (5, sorted.reverse)
        else if straight then (4, [straightHigh rs])
        else
          match sortCounts (rankCounts rs) with
          | (3, _) :: _ => (3, keyCounts)
          | (2, _) :: (2, _) :: _ => (2, keyCounts)
          | (2, _) :: _ => (1, keyCounts)
          | _ => (0, sorted.reverse)

/-- Lexicographic greater-than for lists. -/
def lexGT : List Nat → List Nat → Bool
  | [], _ => false
  | _, [] => false
  | a :: as, b :: bs => if a = b then lexGT as bs else a > b

/-- Whether hand `h1` beats `h2`. -/
def beats (h1 h2 : List Card) : Bool :=
  let s1 := handScore h1
  let s2 := handScore h2
  if s1.1 = s2.1 then lexGT s1.2 s2.2 else s1.1 > s2.1

/-- Count how many hands Player 1 wins in the input. -/
def naive (hands : List (List Card × List Card)) : Nat :=
  hands.foldl (fun acc h => if beats h.1 h.2 then acc + 1 else acc) 0

end ProjectEulerStatements.P54
