import ProjectEulerStatements.Lib.DecimalDigits

/-! Decimal character summation agrees with the sum of positional digits. -/
namespace ProjectEulerStatements.DecimalDigits

lemma foldl_digitChars_sum_aux (xs : List Nat) (acc : Nat) (hxs : ∀ d ∈ xs, d < 10) :
    (xs.map Nat.digitChar).foldl (fun acc c => acc + (c.toNat - '0'.toNat)) acc =
      acc + xs.sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      have hx : x < 10 := hxs x (by simp)
      have htail : ∀ d ∈ xs, d < 10 := by intro d hd; exact hxs d (by simp [hd])
      rw [List.map_cons, List.foldl_cons,
        ih (acc + ((Nat.digitChar x).toNat - '0'.toNat)) htail]
      rw [digitChar_val x hx]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma foldl_digitChars_sum (xs : List Nat) (hxs : ∀ d ∈ xs, d < 10) :
    (xs.map Nat.digitChar).foldl (fun acc c => acc + (c.toNat - '0'.toNat)) 0 =
      xs.sum := by
  simpa using foldl_digitChars_sum_aux xs 0 hxs

lemma sum_string_digits (n : Nat) :
    (toString n).toList.foldl (fun acc c => acc + (c.toNat - '0'.toNat)) 0 =
      (Nat.digits 10 n).sum := by
  by_cases hn : n = 0
  · subst n
    rw [show (toString 0).toList = Nat.toDigits 10 0 by simp, Nat.toDigits_zero]
    decide
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hdigits : ∀ d ∈ (Nat.digits 10 n).reverse, d < 10 := by
      intro d hd
      simpa using (Nat.digits_lt_base (b := 10) (m := n) (d := d) (by norm_num)
        (by simpa using hd))
    rw [show (toString n).toList = Nat.toDigits 10 n by simp]
    rw [toDigits_eq_digitChars n hnpos]
    rw [foldl_digitChars_sum (Nat.digits 10 n).reverse hdigits]
    exact List.sum_reverse (Nat.digits 10 n)


end ProjectEulerStatements.DecimalDigits
