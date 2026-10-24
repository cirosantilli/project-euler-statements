import ProjectEulerStatements.P39
import ProjectEulerStatements.Lib.ArgMaximum
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum

/-! The reference count and the optimized loop table, for arbitrary bounds. -/
namespace ProjectEulerStatements.PythagoreanPerimeterCounting

set_option Elab.async false

/-- The reference uses natural subtraction in its mathematical statement. -/
def triangle (p a b : Nat) : Prop :=
  a < b ∧ b < p - a - b ∧ a ^ 2 + b ^ 2 = (p - a - b) ^ 2

instance (p a b : Nat) : Decidable (triangle p a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Python subtraction agrees on every accepted candidate, even though it can
be negative on rejected candidates. -/
theorem integer_guard (p a b : Nat) :
    ((a : Int) < b ∧ (b : Int) < (p : Int) - a - b ∧
      (a : Int) ^ 2 + (b : Int) ^ 2 = ((p : Int) - a - b) ^ 2) ↔ triangle p a b := by
  by_cases bounded : a + b ≤ p
  · have cast : ((p - a - b : Nat) : Int) = (p : Int) - a - b := by omega
    rw [← cast]
    unfold triangle
    norm_cast
  · have clipped : p - a - b = 0 := by omega
    simp only [triangle, clipped, Nat.not_lt_zero, false_and, and_false, iff_false]
    omega

def solutionPairs (p : Nat) : Finset (Nat × Nat) :=
  ((Finset.range (p + 1)).product (Finset.range (p + 1))).filter
    (fun pair => triangle p pair.1 pair.2)

private theorem fold_count {α : Type*} (items : List α) (predicate : α → Prop)
    [DecidablePred predicate] (initial : Nat) :
    items.foldl (fun total item => if predicate item then total + 1 else total) initial =
      initial + (items.filter (fun item => decide (predicate item))).length := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
      by_cases accepted : predicate head <;> simp [accepted, ih, Nat.add_assoc, Nat.add_comm]

private theorem nested_count (p : Nat) (items : List Nat) (initial : Nat) :
    items.foldl (fun total a => (List.range (p + 1)).foldl
      (fun current b => if triangle p a b then current + 1 else current) total) initial =
      initial + ((items.product (List.range (p + 1))).filter
        (fun pair => decide (triangle p pair.1 pair.2))).length := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail ih =>
      have productCons : (head :: tail).product (List.range (p + 1)) =
          (List.range (p + 1)).map (fun b => (head, b)) ++ tail.product (List.range (p + 1)) := rfl
      rw [List.foldl_cons, fold_count, ih, productCons]
      simp only [List.filter_append, List.length_append, List.filter_map, List.length_map,
        Function.comp_def]
      omega

theorem countSolutions_card (p : Nat) : P39.countSolutions p = (solutionPairs p).card := by
  have counted := nested_count p (List.range (p + 1)) 0
  have distinct : ((List.range (p + 1)).product (List.range (p + 1))).Nodup :=
    (List.nodup_range (n := p + 1)).product (List.nodup_range (n := p + 1))
  have filtered := distinct.filter (fun pair => decide (triangle p pair.1 pair.2))
  have converted : (((List.range (p + 1)).product (List.range (p + 1))).filter
      (fun pair => decide (triangle p pair.1 pair.2))).toFinset = solutionPairs p := by
    ext ⟨a, b⟩
    simp [solutionPairs]
  calc
    P39.countSolutions p = (((List.range (p + 1)).product (List.range (p + 1))).filter
        (fun pair => decide (triangle p pair.1 pair.2))).length := by
      simpa only [P39.countSolutions, triangle, Nat.zero_add] using counted
    _ = (solutionPairs p).card := by
      rw [← converted]
      exact (List.toFinset_card_of_nodup filtered).symm

theorem countSolutions_zero : P39.countSolutions 0 = 0 := rfl

theorem naive_scan (limit : Nat) : P39.naive limit =
    (List.range' 1 limit).foldl
      (ProjectEulerStatements.ArgMaximum.select P39.countSolutions) 0 := by
  unfold P39.naive P39.maxPerimeter
  rw [ProjectEulerStatements.ArgMaximum.argmax_range_succ]

abbrev Table := Nat → Nat

def perimeter (m n : Nat) : Nat := 2 * m * (m + n)
def permitted (limit m n : Nat) : Bool :=
  decide ((m - n) % 2 = 1 ∧ Nat.Coprime m n ∧ perimeter m n ≤ limit)
def increment (table : Table) (perimeter : Nat) : Table :=
  fun p => if p = perimeter then table p + 1 else table p

def addMultiples (_limit m n first count : Nat) (table : Table) : Table :=
  (List.range' first count).foldl (fun table k => increment table (k * perimeter m n)) table

def row (limit m first count : Nat) (table : Table) : Table :=
  (List.range' first count).foldl (fun table n =>
    if permitted limit m n then addMultiples limit m n 1 (limit / perimeter m n) table
    else table) table

def outer (limit first count : Nat) (table : Table) : Table :=
  (List.range' first count).foldl (fun table m =>
    if 2 * m * (m + 1) ≤ limit then row limit m 1 (m - 1) table else table) table

@[simp] theorem addMultiples_zero (limit m n first : Nat) (table : Table) :
    addMultiples limit m n first 0 table = table := rfl

theorem addMultiples_step (limit m n first count : Nat) (table : Table) :
    addMultiples limit m n first (count + 1) table =
      addMultiples limit m n (first + 1) count (increment table (first * perimeter m n)) := by
  simp [addMultiples, List.range'_succ]

@[simp] theorem row_zero (limit m first : Nat) (table : Table) :
    row limit m first 0 table = table := rfl

theorem row_step (limit m first count : Nat) (table : Table) :
    row limit m first (count + 1) table = row limit m (first + 1) count
      (if permitted limit m first then addMultiples limit m first 1 (limit / perimeter m first)
        table else table) := by
  simp [row, List.range'_succ]

@[simp] theorem outer_zero (limit first : Nat) (table : Table) :
    outer limit first 0 table = table := rfl

theorem outer_step (limit first count : Nat) (table : Table) :
    outer limit first (count + 1) table = outer limit (first + 1) count
      (if 2 * first * (first + 1) ≤ limit then row limit first 1 (first - 1) table else table) := by
  simp [outer, List.range'_succ]

theorem outer_inactive (limit first count : Nat) (table : Table)
    (stopped : limit < 2 * first * (first + 1)) : outer limit first count table = table := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
      rw [outer_step, if_neg (by omega)]
      apply ih
      have growth : 2 * first * (first + 1) ≤ 2 * (first + 1) * (first + 1 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
      omega

/-- Actual while-loop starting state; inactive larger parameters contribute no updates. -/
def table (limit : Nat) : Table := outer limit 2 (limit - 1) (fun _ => 0)

end ProjectEulerStatements.PythagoreanPerimeterCounting
