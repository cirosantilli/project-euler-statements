import ProjectEulerStatements.Lib.TotientReference

/-! Least totient-ratio maximizers for arbitrary signed inclusive bounds. -/
namespace ProjectEulerStatements.P69
open TotientMaximum

def phi (n : Nat) : Nat :=
  ((Finset.Icc 1 n).filter (fun k => Nat.gcd k n = 1)).card

theorem phi_eq_totient (n : Nat) : phi n = n.totient := by
  unfold phi
  calc
    _ = ((Finset.Ico 1 (1 + n)).filter (fun k => n.Coprime k)).card := by
      congr 1
      apply Finset.ext
      intro k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico,
        Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm k n]
      omega
    _ = n.totient := Nat.filter_coprime_Ico_eq_totient n 1

def better (a b : Nat) : Bool :=
  if phi a = 0 ∨ phi b = 0 then false else a * phi b > b * phi a

theorem better_eq (a b : Nat) : better a b = TotientMaximum.better a b := by
  simp only [better, TotientMaximum.better, phi_eq_totient]

def bestN (limit : Int) : Nat :=
  (List.range (limit + 1).toNat).foldl (fun best n => if better n best then n else best) 1

def naive (limit : Int) : Nat := bestN limit

theorem naive_eq_reference (limit : Int) : naive limit = referenceResult limit := by
  by_cases negative : limit < 0
  · have empty : (limit + 1).toNat = 0 := by omega
    have clipped : limit.toNat = 0 := by omega
    simp only [naive, bestN, empty, List.range_zero, List.foldl_nil,
      referenceResult, clipped, bestUpTo_zero]
  · have count : (limit + 1).toNat = limit.toNat + 1 := by omega
    simp only [naive, bestN, better_eq]
    change (List.range (limit + 1).toNat).foldl visit 1 = _
    rw [count, fold_range_best]
    rfl

end ProjectEulerStatements.P69
