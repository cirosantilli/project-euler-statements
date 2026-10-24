import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Init.Data.String.Lemmas.Intercalate
import Init.Data.Nat.ToString

/-! Line sums and encoding lengths for magic rings of arbitrary finite size. -/
namespace ProjectEulerStatements.MagicRing
set_option Elab.async false

def triples (outer inner next : List Nat) : List (Nat × Nat × Nat) :=
  outer.zipWith (fun value pair => (value, pair.1, pair.2)) (inner.zip next)

def cycle (outer inner : List Nat) : List (Nat × Nat × Nat) :=
  triples outer inner (inner.rotate 1)

structure Ring (n : Nat) where
  outer : List Nat
  inner : List Nat
  outer_length : outer.length = n
  inner_length : inner.length = n
  labels : (outer ++ inner).Perm (List.range' 1 (2 * n))

theorem triples_length (outer inner next : List Nat)
    (same : outer.length = inner.length) (sameNext : outer.length = next.length) :
    (triples outer inner next).length = outer.length := by
  simp [triples, ← same, ← sameNext]

theorem weighted_triples (weight : Nat → Nat) (outer inner next : List Nat)
    (same : outer.length = inner.length) (sameNext : outer.length = next.length) :
    ((triples outer inner next).map (fun triple =>
      weight triple.1 + weight triple.2.1 + weight triple.2.2)).sum =
      (outer.map weight).sum + (inner.map weight).sum + (next.map weight).sum := by
  induction outer generalizing inner next with
  | nil =>
      have innerNil : inner = [] := List.eq_nil_of_length_eq_zero (by simpa using same.symm)
      have nextNil : next = [] := List.eq_nil_of_length_eq_zero (by simpa using sameNext.symm)
      simp [innerNil, nextNil, triples]
  | cons value rest ih =>
      cases inner with
      | nil => simp at same
      | cons first tail =>
          cases next with
          | nil => simp at sameNext
          | cons second nextTail =>
              have shorter := ih tail nextTail (by simpa using same) (by simpa using sameNext)
              simpa [triples, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                congrArg (fun total => weight value + weight first + weight second + total) shorter

theorem cycle_length {n : Nat} (ring : Ring n) : (cycle ring.outer ring.inner).length = n := by
  rw [cycle, triples_length, ring.outer_length]
  · rw [ring.outer_length, ring.inner_length]
  · simp [ring.outer_length, ring.inner_length]

theorem weighted_cycle {n : Nat} (ring : Ring n) (weight : Nat → Nat) :
    ((cycle ring.outer ring.inner).map (fun triple =>
      weight triple.1 + weight triple.2.1 + weight triple.2.2)).sum =
      (ring.outer.map weight).sum + 2 * (ring.inner.map weight).sum := by
  rw [cycle, weighted_triples weight ring.outer ring.inner (ring.inner.rotate 1)
    (by rw [ring.outer_length, ring.inner_length]) (by simp [ring.outer_length, ring.inner_length])]
  rw [((List.rotate_perm ring.inner 1).map weight).sum_eq]
  omega

theorem label_total (n : Nat) : (List.range' 1 (2 * n)).sum = n * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 2 by omega,
        ← List.range'_append_1 (s := 1) (m := 2 * n) (n := 2), List.sum_append, ih]
      simp [List.range']
      ring

def Magic {n : Nat} (ring : Ring n) (target : Nat) : Prop :=
  ∀ triple ∈ cycle ring.outer ring.inner, triple.1 + triple.2.1 + triple.2.2 = target

theorem sum_constant (items : List α) (value : α → Nat) (target : Nat)
    (constant : ∀ item ∈ items, value item = target) :
    (items.map value).sum = items.length * target := by
  induction items with
  | nil => simp
  | cons first rest ih =>
      rw [List.map_cons, List.sum_cons, constant first List.mem_cons_self,
        ih (by intro item member; exact constant item (List.mem_cons_of_mem _ member))]
      simp [Nat.add_mul, Nat.add_comm]

/-- Each inner label contributes twice to the sum of the line totals. -/
theorem target_formula {n : Nat} (ring : Ring n) (target : Nat) (magic : Magic ring target) :
    n * target = n * (2 * n + 1) + ring.inner.sum := by
  have lines := weighted_cycle ring (fun value => value)
  have constant := sum_constant (cycle ring.outer ring.inner)
    (fun triple => triple.1 + triple.2.1 + triple.2.2) target magic
  have labels := ring.labels.sum_eq
  rw [List.sum_append, label_total] at labels
  simp only [List.map_id', cycle_length] at lines constant
  omega

theorem sum_mod_eq_zero {n : Nat} (ring : Ring n) (target : Nat) (magic : Magic ring target) :
    (n * (2 * n + 1) + ring.inner.sum) % n = 0 := by
  exact Nat.mod_eq_zero_of_dvd ⟨target, (target_formula ring target magic).symm⟩

theorem target_eq_quotient {n : Nat} (ring : Ring n) (positive : 0 < n)
    (target : Nat) (magic : Magic ring target) :
    target = (n * (2 * n + 1) + ring.inner.sum) / n := by
  rw [← target_formula ring target magic, Nat.mul_div_cancel_left target positive]

theorem forced_outer {n : Nat} (ring : Ring n) (target : Nat) (magic : Magic ring target)
    (triple : Nat × Nat × Nat) (member : triple ∈ cycle ring.outer ring.inner) :
    triple.1 = target - triple.2.1 - triple.2.2 := by
  have equation := magic triple member
  omega

def digitWidth (value : Nat) : Nat := (toString (value : Int)).toList.length

theorem digitWidth_positive (value : Nat) : 0 < digitWidth value := by
  simpa [digitWidth, toString, Int.repr, Nat.repr] using
    (Nat.length_toDigits_pos (b := 10) (n := value))

theorem width_sum_lower (items : List Nat) : items.length ≤ (items.map digitWidth).sum := by
  induction items with
  | nil => simp
  | cons first rest ih =>
      have positive := digitWidth_positive first
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

def text (outer inner : List Nat) : String := String.join ((cycle outer inner).map
  (fun triple => toString (triple.1 : Int) ++ toString (triple.2.1 : Int) ++
    toString (triple.2.2 : Int)))

theorem join_length (parts : List String) :
    (String.join parts).toList.length = (parts.map (fun part => part.toList.length)).sum := by
  induction parts with
  | nil => rfl
  | cons first rest ih => simp_all

/-- The canonical representation repeats precisely the inner labels. -/
theorem text_length {n : Nat} (ring : Ring n) :
    (text ring.outer ring.inner).toList.length =
      ((List.range' 1 (2 * n)).map digitWidth).sum + (ring.inner.map digitWidth).sum := by
  have lines := weighted_cycle ring digitWidth
  have labels := (ring.labels.map digitWidth).sum_eq
  rw [List.map_append, List.sum_append] at labels
  rw [text, join_length, List.map_map]
  have same : ((cycle ring.outer ring.inner).map (fun triple =>
      (toString (triple.1 : Int) ++ toString (triple.2.1 : Int) ++
        toString (triple.2.2 : Int)).toList.length)).sum =
      (ring.outer.map digitWidth).sum + 2 * (ring.inner.map digitWidth).sum := by
    simpa only [String.toList_append, List.length_append, digitWidth] using lines
  simpa only [Function.comp_def] using (same.trans (by omega))

theorem text_min_length {n : Nat} (ring : Ring n) :
    3 * n ≤ (text ring.outer ring.inner).toList.length := by
  rw [text_length]
  have labels := width_sum_lower (List.range' 1 (2 * n))
  have inner := width_sum_lower ring.inner
  rw [List.length_range'] at labels
  rw [ring.inner_length] at inner
  omega

end ProjectEulerStatements.MagicRing
