import ProjectEulerStatements.Lib.SqrtReducedStates
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-! Finite reduced-state orbits prove termination of an unbounded square-root period search. -/
namespace ProjectEulerStatements.SqrtReducedStates
set_option Elab.async false

abbrev ReducedState (n root : Int) := {state : State // Reduced n root state}

instance (n root : Int) : Fintype (ReducedState n root) :=
  Fintype.ofFinset
    ((Finset.Icc 0 root ×ˢ Finset.Icc 1 (2 * root)).filter (Reduced n root)) (by
      intro state
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      constructor
      · exact fun member => member.2
      · intro valid
        have nonneg := valid.1
        have upper := valid.2.1
        have positive := valid.2.2.1
        have denominatorUpper := valid.2.2.2.2.1
        exact ⟨⟨⟨nonneg, upper⟩, ⟨by omega, by omega⟩⟩, valid⟩)

def move {n root : Int} (bounds : Bounds n root) (state : ReducedState n root) :
    ReducedState n root :=
  ⟨step n root state.val, step_reduced bounds state.property⟩

def origin {n root : Int} (bounds : Bounds n root) : ReducedState n root :=
  ⟨first n root, first_reduced bounds⟩

theorem move_injective {n root : Int} (bounds : Bounds n root) :
    Function.Injective (move bounds) := by
  intro left right same
  apply Subtype.ext
  exact step_injective bounds left.property right.property (congrArg Subtype.val same)

theorem iterate_value {n root : Int} (bounds : Bounds n root) (state : ReducedState n root)
    (index : Nat) :
    ((move bounds)^[index] state).val = (step n root)^[index] state.val := by
  induction index with
  | zero => rfl
  | succ index ih =>
      simp only [Function.iterate_succ_apply', move, ih]

/-- A finite injective orbit returns to its origin, rather than merely entering some other cycle. -/
theorem exists_period {n root : Int} (bounds : Bounds n root) :
    ∃ index : Nat, 0 < index ∧ (step n root)^[index] (first n root) = first n root := by
  obtain ⟨index, positive, same⟩ := Function.mem_periodicPts.mp
    ((move_injective bounds).mem_periodicPts (origin bounds))
  refine ⟨index, positive, ?_⟩
  simpa only [iterate_value, origin] using congrArg Subtype.val same

/-- The least return time uses a decidable equality test and a proved existence witness. -/
def period {n root : Int} (bounds : Bounds n root) : Nat := Nat.find (exists_period bounds)

theorem period_positive {n root : Int} (bounds : Bounds n root) : 0 < period bounds :=
  (Nat.find_spec (exists_period bounds)).1

theorem period_returns {n root : Int} (bounds : Bounds n root) :
    (step n root)^[period bounds] (first n root) = first n root :=
  (Nat.find_spec (exists_period bounds)).2

theorem period_minimal {n root : Int} (bounds : Bounds n root) (index : Nat) (positive : 0 < index)
    (same : (step n root)^[index] (first n root) = first n root) : period bounds ≤ index :=
  Nat.find_min' (exists_period bounds) ⟨positive, same⟩

theorem orbit_reduced {n root : Int} (bounds : Bounds n root) (index : Nat) :
    Reduced n root ((step n root)^[index] (first n root)) := by
  induction index with
  | zero => exact first_reduced bounds
  | succ index ih => simpa only [Function.iterate_succ_apply'] using step_reduced bounds ih

theorem terminal_at_period {n root : Int} (bounds : Bounds n root) :
    (step n root)^[period bounds - 1] (first n root) = terminal root := by
  apply step_injective bounds (orbit_reduced bounds _) (terminal_reduced bounds)
  rw [← Function.iterate_succ_apply' (step n root) (period bounds - 1) (first n root),
    show (period bounds - 1).succ = period bounds by have := period_positive bounds; omega,
    period_returns, step_terminal]

theorem before_terminal {n root : Int} (bounds : Bounds n root) (index : Nat)
    (before : index + 1 < period bounds) :
    (step n root)^[index] (first n root) ≠ terminal root := by
  intro same
  have returned : (step n root)^[index + 1] (first n root) = first n root := by
    rw [Function.iterate_succ_apply', same, step_terminal]
  have minimal := period_minimal bounds (index + 1) (by omega) returned
  omega

/-- No two states preceding the first return are equal. -/
theorem orbit_injective {n root : Int} (bounds : Bounds n root) (left right : Nat)
    (leftBefore : left < period bounds) (rightBefore : right < period bounds)
    (same : (step n root)^[left] (first n root) = (step n root)^[right] (first n root)) :
    left = right := by
  wlog ordered : right ≤ left generalizing left right
  · exact (this right left rightBefore leftBefore same.symm (by omega)).symm
  have equal : (move bounds)^[left] (origin bounds) = (move bounds)^[right] (origin bounds) := by
    apply Subtype.ext
    simpa only [iterate_value, origin] using same
  have cancelled := Function.iterate_cancel (move_injective bounds) equal
  have returned : (step n root)^[left - right] (first n root) = first n root := by
    simpa only [iterate_value, origin] using congrArg Subtype.val cancelled
  by_contra different
  have minimal := period_minimal bounds (left - right) (by omega) returned
  omega

theorem period_bounded {n root : Int} (bounds : Bounds n root) :
    period bounds ≤ Fintype.card (ReducedState n root) := by
  have injective : Function.Injective (fun index : Fin (period bounds) =>
      (move bounds)^[index.val] (origin bounds)) := by
    intro left right same
    apply Fin.ext
    apply orbit_injective bounds left.val right.val left.isLt right.isLt
    simpa only [iterate_value, origin] using congrArg Subtype.val same
  simpa using Fintype.card_le_of_injective _ injective

end ProjectEulerStatements.SqrtReducedStates
