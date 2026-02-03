import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace ProjectEulerStatements.P30

def digitPowerSum (p n : Nat) : Nat :=
  (Nat.digits 10 n).foldl (fun acc d => acc + d ^ p) 0

def sumPowerDigits (p : Nat) (nums : List Nat) : Nat :=
  nums.foldl
    (fun acc n =>
      if n = 1 then acc
      else if digitPowerSum p n = n then acc + n else acc)
    0

def limit (p : Nat) : Nat :=
  (p + 2) * 9 ^ p

/-- Sum of all numbers equal to the sum of their digits to power `p`. -/
def naive (p : Nat) : Nat :=
  sumPowerDigits p (List.range (limit p + 1))

lemma foldl_add_eq_sum (l : List Nat) (init : Nat) (f : Nat → Nat) :
    l.foldl (fun acc d => acc + f d) init = init + (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a tl ih =>
      simp [List.foldl, ih, Nat.add_assoc]

lemma sum_le_mul_of_forall_le (l : List Nat) (M : Nat) (h : ∀ x ∈ l, x ≤ M) :
    l.sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a tl ih =>
      have ha : a ≤ M := h _ (by simp)
      have htl : ∀ x ∈ tl, x ≤ M := by
        intro x hx
        exact h _ (by simp [hx])
      have ih' := ih htl
      have hsum : a + tl.sum ≤ M + tl.length * M := Nat.add_le_add ha ih'
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum

lemma digitPowerSum_le (p n : Nat) :
    digitPowerSum p n ≤ (Nat.digits 10 n).length * 9 ^ p := by
  let l := (Nat.digits 10 n).map (fun d => d ^ p)
  have hmem : ∀ x ∈ l, x ≤ 9 ^ p := by
    intro x hx
    rcases (List.mem_map).1 hx with ⟨d, hd, rfl⟩
    have hdlt : d < 10 := Nat.digits_lt_base (by decide : 1 < 10) hd
    have hdle : d ≤ 9 := Nat.le_of_lt_succ hdlt
    exact Nat.pow_le_pow_left hdle p
  have hsum : l.sum ≤ l.length * 9 ^ p := sum_le_mul_of_forall_le _ _ hmem
  have hlen : l.length = (Nat.digits 10 n).length := by simp [l]
  simpa [digitPowerSum, foldl_add_eq_sum, l, hlen] using hsum

lemma two_p_plus_three_lt_ten_pow (p : Nat) : 2 * p + 3 < 10 ^ (p + 2) := by
  induction p with
  | zero =>
      simp
  | succ p ih =>
      have h1 : 2 * p + 3 < 10 ^ (p + 2) := ih
      have h2 : 2 * p + 5 < 10 * (2 * p + 3) := by omega
      have h3 : 10 * (2 * p + 3) < 10 * 10 ^ (p + 2) := by
        exact Nat.mul_lt_mul_of_pos_left h1 (by decide : 0 < 10)
      have h4 : 2 * p + 5 < 10 * 10 ^ (p + 2) := lt_trans h2 h3
      have h4' : 2 * (p + 1) + 3 = 2 * p + 5 := by omega
      have h4'' : 2 * (p + 1) + 3 < 10 * 10 ^ (p + 2) := by
        simpa [h4'] using h4
      have hpow : 10 * 10 ^ (p + 2) = 10 ^ (p + 3) := by
        calc
          10 * 10 ^ (p + 2) = 10 ^ (p + 2) * 10 := by
            simp [Nat.mul_comm]
          _ = 10 ^ ((p + 2) + 1) := by simp [pow_succ]
          _ = 10 ^ (p + 3) := by simp [Nat.add_assoc]
      simpa [hpow] using h4''

lemma mul_nine_pow_lt_ten_pow (p : Nat) : (2 * p + 3) * 9 ^ p < 10 ^ (2 * p + 2) := by
  have h1 : 2 * p + 3 < 10 ^ (p + 2) := two_p_plus_three_lt_ten_pow p
  have h2 : 9 ^ p ≤ 10 ^ p := Nat.pow_le_pow_left (by decide : 9 ≤ 10) p
  have hpos : 0 < 10 ^ p := Nat.pow_pos (by decide : 0 < 10)
  have hmul : (2 * p + 3) * 9 ^ p < 10 ^ (p + 2) * 10 ^ p :=
    Nat.mul_lt_mul_of_lt_of_le h1 h2 hpos
  have hpow : 10 ^ (p + 2) * 10 ^ p = 10 ^ (2 * p + 2) := by
    have h' : p + 2 + p = 2 * p + 2 := by omega
    have hpow' : 10 ^ (p + 2 + p) = 10 ^ (p + 2) * 10 ^ p := by
      simpa [Nat.add_assoc] using (pow_add 10 (p + 2) p)
    simpa [h'] using hpow'.symm
  simpa [hpow] using hmul

lemma ten_pow_gt_mul (p l : Nat) (hl : 2 * p + 3 ≤ l) : l * 9 ^ p < 10 ^ (l - 1) := by
  induction l, hl using Nat.le_induction with
  | base =>
      have h := mul_nine_pow_lt_ten_pow p
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  | succ l hl ih =>
      have h1 : (l + 1) ≤ 10 * l := by omega
      have h2 : (l + 1) * 9 ^ p ≤ (10 * l) * 9 ^ p :=
        Nat.mul_le_mul_right _ h1
      have h3 : (10 * l) * 9 ^ p < 10 * 10 ^ (l - 1) := by
        have hmul : 10 * (l * 9 ^ p) < 10 * 10 ^ (l - 1) :=
          Nat.mul_lt_mul_of_pos_left ih (by decide : 0 < 10)
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      have h4 : (l + 1) * 9 ^ p < 10 * 10 ^ (l - 1) := lt_of_le_of_lt h2 h3
      have hpos : 0 < l := by omega
      have hpred : l - 1 + 1 = l := Nat.succ_pred_eq_of_pos hpos
      have hpow : 10 * 10 ^ (l - 1) = 10 ^ l := by
        calc
          10 * 10 ^ (l - 1) = 10 ^ (l - 1) * 10 := by
            simp [Nat.mul_comm]
          _ = 10 ^ ((l - 1) + 1) := by simp [pow_succ]
          _ = 10 ^ l := by simp [hpred]
      simpa [hpow] using h4

lemma digits_length_ge_of_pow_le (p n : Nat) (hge : 10 ^ (2 * p + 2) ≤ n) :
    2 * p + 3 ≤ (Nat.digits 10 n).length := by
  by_contra hlt
  have hlt' : (Nat.digits 10 n).length < 2 * p + 3 := lt_of_not_ge hlt
  have hle : (Nat.digits 10 n).length ≤ 2 * p + 2 := Nat.le_of_lt_succ hlt'
  have hlt' : n < 10 ^ (Nat.digits 10 n).length := by
    simpa using (Nat.lt_base_pow_length_digits' (b := 8) (m := n))
  have hlt'' : n < 10 ^ (2 * p + 2) :=
    lt_of_lt_of_le hlt' (Nat.pow_le_pow_right (by decide : 1 ≤ 10) hle)
  exact (not_lt_of_ge hge) hlt''

lemma pow_len_pred_le (n : Nat) (hn : n ≠ 0) :
    10 ^ ((Nat.digits 10 n).length - 1) ≤ n := by
  have hpow : 10 ^ (Nat.digits 10 n).length ≤ 10 * n :=
    (Nat.base_pow_length_digits_le 10 n (by decide : 1 < 10)) hn
  have hpos : 0 < (Nat.digits 10 n).length := by
    have hnnil : Nat.digits 10 n ≠ [] := (Nat.digits_ne_nil_iff_ne_zero (b := 10)).2 hn
    exact List.length_pos_of_ne_nil hnnil
  have hpred : (Nat.digits 10 n).length - 1 + 1 = (Nat.digits 10 n).length :=
    Nat.succ_pred_eq_of_pos hpos
  have hpow' : 10 * 10 ^ ((Nat.digits 10 n).length - 1) ≤ 10 * n := by
    calc
      10 * 10 ^ ((Nat.digits 10 n).length - 1) =
          10 ^ ((Nat.digits 10 n).length - 1) * 10 := by
            simp [Nat.mul_comm]
      _ = 10 ^ ((Nat.digits 10 n).length - 1 + 1) := by simp [pow_succ]
      _ = 10 ^ (Nat.digits 10 n).length := by simp [hpred]
      _ ≤ 10 * n := hpow
  exact Nat.le_of_mul_le_mul_left hpow' (by decide : 0 < 10)

lemma digitPowerSum_lt_of_large (p n : Nat) (hge : 10 ^ (2 * p + 2) ≤ n) :
    digitPowerSum p n < n := by
  have hn0 : n ≠ 0 := by
    have hpos : 0 < 10 ^ (2 * p + 2) := Nat.pow_pos (by decide : 0 < 10)
    exact ne_of_gt (lt_of_lt_of_le hpos hge)
  have hlen : 2 * p + 3 ≤ (Nat.digits 10 n).length :=
    digits_length_ge_of_pow_le p n hge
  have hpowle : 10 ^ ((Nat.digits 10 n).length - 1) ≤ n := pow_len_pred_le n hn0
  have hsumle : digitPowerSum p n ≤ (Nat.digits 10 n).length * 9 ^ p := digitPowerSum_le p n
  have hsumlt : (Nat.digits 10 n).length * 9 ^ p < 10 ^ ((Nat.digits 10 n).length - 1) :=
    ten_pow_gt_mul p _ hlen
  have hlt : digitPowerSum p n < n := lt_of_le_of_lt hsumle (lt_of_lt_of_le hsumlt hpowle)
  exact hlt

theorem finite_power_digit_sums (p : Nat) :
    {n | digitPowerSum p n = n ∧ n ≠ 1}.Finite := by
  classical
  refine (Set.finite_Icc 0 (10 ^ (2 * p + 2) - 1)).subset ?_
  intro n hn
  have hfix : digitPowerSum p n = n := hn.1
  have hlt : n < 10 ^ (2 * p + 2) := by
    by_contra hge
    have hge' : 10 ^ (2 * p + 2) ≤ n := Nat.le_of_not_lt hge
    have hlt' : digitPowerSum p n < n := digitPowerSum_lt_of_large p n hge'
    have hnot : ¬ digitPowerSum p n < n := by
      simp [hfix]
    exact (hnot hlt')
  have hle : n ≤ (10 ^ (2 * p + 2) - 1) := Nat.le_pred_of_lt hlt
  exact ⟨by exact Nat.zero_le _, hle⟩

example : naive 4 = 19316 := by
  native_decide

end ProjectEulerStatements.P30
