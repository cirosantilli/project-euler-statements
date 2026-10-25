import ProjectEulerStatements.P69
import ProjectEulerStatements.Lib.TotientPermutationMinimum

/-! Least decimal totient-permutation ratio minimizers for arbitrary signed inclusive bounds. -/
namespace ProjectEulerStatements.P70

def phi (n : Nat) : Nat :=
  ((Finset.Icc 1 n).filter (fun k => Nat.gcd k n = 1)).card

theorem phi_eq_totient (n : Nat) : phi n = n.totient := P69.phi_eq_totient n

def digitsSorted (n : Nat) : List Nat :=
  (Nat.digits 10 n).mergeSort (fun a b => decide (a ≤ b))

def isPermutation (a b : Nat) : Bool := digitsSorted a = digitsSorted b

theorem isPermutation_eq (a b : Nat) :
    isPermutation a b = TotientPermutation.isPermutation a b := rfl

def better (a b : Nat) : Bool :=
  if phi a = 0 ∨ phi b = 0 then false else a * phi b < b * phi a

theorem better_eq (a b : Nat) : better a b = TotientPermutation.better a b := by
  simp only [better, TotientPermutation.better, phi_eq_totient]

theorem update_eq (best n : Nat) :
    (if decide (n > 1) && isPermutation n (phi n) then
      if decide (best = 0) || better n best then n else best
    else best) = TotientPermutation.visit best n := by
  simp only [phi_eq_totient, isPermutation_eq, better_eq, TotientPermutation.visit,
    TotientPermutation.eligible, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  rfl

def bestN (limit : Int) : Nat :=
  (List.range (limit + 1).toNat).foldl (fun best n =>
    if decide (n > 1) && isPermutation n (phi n) then
      if decide (best = 0) || better n best then n else best
    else best) 0

def naive (limit : Int) : Nat := bestN limit

theorem naive_eq_reference (limit : Int) : naive limit = TotientPermutation.result limit := by
  simp only [naive, bestN, update_eq]
  exact TotientPermutation.signed_fold limit

end ProjectEulerStatements.P70
