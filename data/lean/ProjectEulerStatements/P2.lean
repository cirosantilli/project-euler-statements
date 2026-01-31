import Mathlib

namespace ProjectEulerStatements.P2

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

def fib : Nat -> Nat
  | 0       => 1
  | 1       => 2
  | n + 2   => fib (n) + fib (n + 1)

theorem fib_ge_succ (n : Nat) : n + 1 ≤ fib n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  cases n with
  | zero =>
      simp [fib]
  | succ n =>
      cases n with
      | zero =>
          simp [fib]
      | succ n =>
          have ih_n : n + 1 ≤ fib n := ih n (by omega)
          have ih_n1 : n + 2 ≤ fib (n + 1) := ih (n + 1) (by omega)
          have hsum : (n + 1) + (n + 2) ≤ fib n + fib (n + 1) :=
            add_le_add ih_n ih_n1
          have hstep : n + 3 ≤ (n + 1) + (n + 2) := by omega
          have h' : n + 3 ≤ fib n + fib (n + 1) := le_trans hstep hsum
          simpa [fib, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h'

theorem fib_eq_nat_fib_aux :
    ∀ n, fib n = Nat.fib (n + 2) ∧ fib (n + 1) = Nat.fib (n + 3) := by
  intro n
  induction n with
  | zero =>
      constructor
      · simp [fib]
      · simp [fib, Nat.fib_add_two]
  | succ n ih =>
      constructor
      · exact ih.2
      · calc
          fib (n + 2) = fib n + fib (n + 1) := by
            simp [fib]
          _ = Nat.fib (n + 2) + Nat.fib (n + 3) := by
            simp [ih.1, ih.2]
          _ = Nat.fib (n + 4) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              (Nat.fib_add_two (n := n + 2)).symm

theorem fib_eq_nat_fib (n : Nat) : fib n = Nat.fib (n + 2) :=
  (fib_eq_nat_fib_aux n).1

/-- Sum of the even-valued Fibonacci numbers which do not exceed `n` -/
def naive (n : Nat) : Nat :=
  let rec go (i total : Nat) : Nat :=
    let f := fib i
    if f <= n then
      go (i + 1) (if f % 2 = 0 then total + f else total)
    else
      total
  termination_by n + 1 - i
  decreasing_by
    have hi' : i + 1 ≤ n := le_trans (fib_ge_succ i) (by simpa using ‹_›)
    omega
  go 0 0

noncomputable def naive2 (n : Nat) : Nat := by
  classical
  let S : Set Nat := {x | (∃ i, fib i = x) ∧ x ≤ n ∧ x % 2 = 0}
  have hfin : S.Finite := by
    refine (Set.finite_le_nat n).subset ?_
    intro x hx
    exact hx.2.1
  exact ∑ x ∈ hfin.toFinset, x

theorem naive_eq_naive2 (n : Nat) : naive n = naive2 n := by
  -- By definition of `naive`, we have:
  have h_naive_def : naive n = ∑ i ∈ Finset.range (Nat.find (show ∃ i, fib i > n from Exists.elim (show ∃ i, fib i > n from by
                                                                                                    exact ⟨ n + 2, by linarith [ fib_ge_succ ( n + 2 ) ] ⟩) fun i hi => ⟨i, hi⟩)), (if fib i ≤ n ∧ fib i % 2 = 0 then fib i else 0) := by
                                                                                                    -- Let's unfold the definition of `naive`.
                                                                                                    unfold naive;
                                                                                                    -- By definition of `naive.go`, we can rewrite the left-hand side of the equation.
                                                                                                    have h_naive_go : ∀ i total, naive.go n i total = ∑ j ∈ Finset.range (Nat.find (show ∃ i, fib i > n from by
                                                                                                                                                                                      -- Since the Fibonacci sequence is unbounded, there exists some $i$ such that $fib(i) > n$.
                                                                                                                                                                                      have h_unbounded : ∃ i, fib i > n := by
                                                                                                                                                                                        have h_unbounded : ∀ M : ℕ, ∃ i, fib i > M := by
                                                                                                                                                                                          intro M;
                                                                                                                                                                                          induction' M with M ih;
                                                                                                                                                                                          · exists 0;
                                                                                                                                                                                          · obtain ⟨ i, hi ⟩ := ih;
                                                                                                                                                                                            exact ⟨ i + 2, by linarith [ show fib ( i + 2 ) > fib i from by { exact ( show fib ( i + 2 ) > fib i from by { exact ( by { rw [ show fib ( i + 2 ) = fib i + fib ( i + 1 ) from by rfl ] ; linarith [ show fib ( i + 1 ) > 0 from Nat.recOn i ( by trivial ) fun i hi => by { rw [ show fib ( i + 2 ) = fib i + fib ( i + 1 ) from by rfl ] ; positivity } ] } ) } ) } ] ⟩
                                                                                                                                                                                        exact h_unbounded n;
                                                                                                                                                                                      exact h_unbounded) - i), (if fib (i + j) ≤ n ∧ fib (i + j) % 2 = 0 then fib (i + j) else 0) + total := by
                                                                                                                                                                                      intros i total;
                                                                                                                                                                                      induction' h : Nat.find ( show ∃ i, fib i > n from ⟨ n + 2, by linarith [ fib_ge_succ ( n + 2 ) ] ⟩ ) - i with k hk generalizing i total;
                                                                                                                                                                                      · unfold naive.go;
                                                                                                                                                                                        -- Since $i \geq \text{Nat.find} (\exists i, \text{fib} i > n)$, we have $\text{fib} i \geq \text{fib} (\text{Nat.find} (\exists i, \text{fib} i > n)) > n$.
                                                                                                                                                                                        have h_fib_i_gt_n : fib i ≥ fib (Nat.find (show ∃ i, fib i > n from ⟨n + 2, by linarith [fib_ge_succ (n + 2)]⟩)) := by
                                                                                                                                                                                                                                    refine' monotone_nat_of_le_succ ( fun n => _ ) ( Nat.le_of_not_lt fun hi => _ );
                                                                                                                                                                                                                                    · rcases n with ( _ | _ | n ) <;> simp +arith +decide [ *, Nat.fib_add_two ];
                                                                                                                                                                                                                                      exact Nat.le_add_left _ _;
                                                                                                                                                                                                                                    · exact absurd h ( Nat.sub_ne_zero_of_lt hi );
                                                                                                                                                                                        exact if_neg ( by linarith [ Nat.find_spec ( show ∃ i, fib i > n from ⟨ n + 2, by linarith [ fib_ge_succ ( n + 2 ) ] ⟩ ) ] ) |> fun h => h.trans ( by norm_num );
                                                                                                                                                                                      · unfold naive.go; simp +decide [ Finset.sum_range_succ', h ] ;
                                                                                                                                                                                        split_ifs <;> simp_all +decide [ Nat.sub_succ, add_comm, add_left_comm, add_assoc ];
                                                                                                                                                                                        -- Since $j + (i + 1)$ is in the set $\{x \mid \text{fib } x > n\}$, the find of this set must be less than or equal to $j + (i + 1)$.
                                                                                                                                                                                        have h_find_le : ∀ x, fib x > n → Nat.find (show ∃ x, fib x > n from ⟨ _, ‹_› ⟩) ≤ x := by
                                                                                                                                                                                                                                      exact fun x hx => Nat.find_min' _ hx;
                                                                                                                                                                                        grind;
                                                                                                    grind;
  -- By definition of `naive2`, we have:
  have h_naive2_def : naive2 n = ∑ i ∈ Finset.filter (fun i => fib i ≤ n ∧ fib i % 2 = 0) (Finset.range (Nat.find (show ∃ i, fib i > n from by
                                                                                                                    grind))), fib i := by
                                                                                                                    -- By definition of `naive2`, we know that it is the sum of the even Fibonacci numbers less than or equal to `n`.
                                                                                                                    have h_naive2_def : naive2 n = ∑ x ∈ Finset.filter (fun x => x ≤ n ∧ x % 2 = 0) (Finset.image fib (Finset.range (Nat.find (show ∃ i, fib i > n from by
                                                                                                                                                                                                                                                grind)))), x := by
                                                                                                                                                                                                                                                refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +contextual;
                                                                                                                                                                                                                                                exact fun a ha₁ ha₂ => ⟨ a, fun m hm => le_trans ( show fib m ≤ fib a from by
                                                                                                                                                                                                                                                                                                    exact monotone_nat_of_le_succ ( fun n => by rcases n with ( _ | _ | n ) <;> { exact Nat.le_add_left _ _ } ) hm ) ha₁, rfl ⟩;
                                                                                                                    rw [ h_naive2_def, Finset.sum_filter, Finset.sum_image ];
                                                                                                                    · rw [ Finset.sum_filter ];
                                                                                                                    · -- The Fibonacci sequence is strictly increasing, so if `fib i = fib j`, then `i = j`.
                                                                                                                      have h_fib_inj : StrictMono fib := by
                                                                                                                        refine' strictMono_nat_of_lt_succ _;
                                                                                                                        intro n; induction n <;> simp_all +arith +decide [ fib ] ;
                                                                                                                        exact Nat.one_le_iff_ne_zero.mpr ( by linarith [ fib_ge_succ ‹_› ] );
                                                                                                                      exact h_fib_inj.injective.injOn;
  rw [ h_naive_def, h_naive2_def, Finset.sum_filter ]

#check naive.go

theorem fib_strictMono : StrictMono fib := by
  intro a b h
  simp only [fib_eq_nat_fib]
  exact Nat.fib_add_two_strictMono h

theorem exists_fib_gt (n : Nat) : ∃ k, fib k > n := by
  use n + 2
  have := fib_ge_succ (n + 2)
  omega

noncomputable def limit (n : Nat) : Nat := Nat.find (exists_fib_gt n)

theorem fib_lt_limit_iff (n k : Nat) : k < limit n ↔ fib k ≤ n := by
  rw [limit]
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    have := Nat.find_min (exists_fib_gt n) h
    contradiction
  · intro h
    by_contra h'
    push_neg at h'
    have : fib (limit n) > n := Nat.find_spec (exists_fib_gt n)
    have : fib k ≥ fib (limit n) := fib_strictMono.monotone h'
    omega

theorem naive2_eq_sum_range (n : Nat) :
    naive2 n = ∑ k ∈ Finset.filter (fun k => fib k % 2 = 0) (Finset.range (limit n)), fib k := by
      -- By definition of $naive2$, we know that
      have h_naive2_def : naive2 n = ∑ x ∈ Finset.image fib (Finset.range (limit n)), if x % 2 = 0 then x else 0 := by
        -- By definition of $naive2$, we know that
        have h_naive2_def : naive2 n = ∑ x ∈ Finset.image fib (Finset.range (limit n)), if x % 2 = 0 then x else 0 := by
          have h_finset : Finset.image fib (Finset.range (limit n)) = Finset.filter (fun x => x ≤ n) (Finset.image fib (Finset.range (limit n))) := by
            -- Since $limit n$ is the smallest index where $fib k$ exceeds $n$, for all $k < limit n$, we have $fib k \leq n$.
            have h_fib_le_n : ∀ k < limit n, fib k ≤ n := by
              exact fun k hk => Nat.le_of_lt_succ ( by linarith [ fib_lt_limit_iff n k |>.1 hk ] );
            grind
          convert Finset.sum_filter _ _ using 2;
          refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +contextual;
          · -- Since $fib$ is strictly increasing, if $fib a \leq n$, then $a < limit n$.
            have h_a_lt_limit : ∀ a, fib a ≤ n → a < limit n := by
              exact fun a ha => Nat.lt_of_not_ge fun h => not_lt_of_ge ha <| Nat.find_spec ( exists_fib_gt n ) |> fun h' => h'.trans_le <| by exact monotone_nat_of_le_succ ( fun n => by exact le_of_lt <| fib_strictMono <| Nat.lt_succ_self n ) h;
            exact fun a ha ha' => ⟨ a, h_a_lt_limit a ha, rfl ⟩;
          · intro a ha h; replace h_finset := Finset.ext_iff.mp h_finset ( fib a ) ; aesop;
        exact h_naive2_def;
      rw [ h_naive2_def, Finset.sum_image ];
      · rw [ Finset.sum_filter ];
      · exact fun x hx y hy hxy => by simpa using StrictMono.injective ( show StrictMono fib from fib_strictMono ) hxy;

theorem naive_go_eq_sum (n i total : Nat) :
    naive.go n i total = total + ∑ k ∈ Finset.filter (fun k => fib k % 2 = 0) (Finset.Ico i (limit n)), fib k := by
  -- We prove this by induction on `limit n - i`
  induction' h : limit n - i using Nat.strong_induction_on with m ih generalizing i total;
  by_cases hi : i < limit n;
  · -- By definition of `naive.go`, we have:
    have h_def : naive.go n i total = if fib i ≤ n then naive.go n (i + 1) (if fib i % 2 = 0 then total + fib i else total) else total := by
      -- By definition of `naive.go`, we have that `naive.go n i total` is equal to the if statement based on `fib i ≤ n` and the recursive call.
      rw [naive.go];
    split_ifs at h_def <;> simp_all +decide [ Nat.sub_add_cancel hi.le ];
    · convert ih ( limit n - ( i + 1 ) ) ( by omega ) ( i + 1 ) ( total + fib i ) rfl using 1;
      rw [ add_assoc, Finset.Ico_eq_cons_Ioo ( by linarith ), Finset.filter_cons ] ; aesop;
    · convert ih ( limit n - ( i + 1 ) ) _ ( i + 1 ) total _ using 1;
      · rw [ Finset.Ico_eq_cons_Ioo ( by linarith ), Finset.filter_cons ] ; aesop;
      · omega;
      · rfl;
    · exact absurd ‹_› ( not_lt_of_ge ( by linarith [ fib_lt_limit_iff n i |>.1 hi ] ) );
  · -- Since $i \geq \text{limit } n$, we have $\text{fib } i > n$, so the if condition in naive.go is false.
    have h_fib_gt_n : fib i > n := by
      exact Nat.find_spec ( exists_fib_gt n ) |> fun h => h.trans_le ( fib_strictMono.monotone ( le_of_not_gt hi ) );
    unfold naive.go; aesop;

theorem naive_eq_naive2_proof (n : Nat) : naive n = naive2 n := by
  rw [naive2_eq_sum_range]
  rw [naive, naive_go_eq_sum]
  simp only [zero_add]
  rw [← Finset.range_eq_Ico]

end ProjectEulerStatements.P2
