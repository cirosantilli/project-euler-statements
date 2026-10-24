import Mathlib.Data.List.GetD
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega

/-! Indexing a concatenation of equal-width blocks without expanding its contents. -/
namespace ProjectEulerStatements.UniformBlocks

set_option Elab.async false

theorem uniform_flatMap_length {α β : Type*} (items : List α) (f : α → List β)
    (width : Nat) (uniform : ∀ x ∈ items, (f x).length = width) :
    (items.flatMap f).length = items.length * width := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      have headWidth := uniform head (by simp)
      have tailWidth : ∀ x ∈ tail, (f x).length = width := by
        intro x member
        exact uniform x (by simp [member])
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        headWidth, ih tailWidth, Nat.add_mul, Nat.one_mul]
      omega

/-- First select a block, then its offset; the default is never used for the block index. -/
theorem uniform_flatMap_block {α β : Type*} (items : List α) (f : α → List β)
    (width : Nat) (fallbackItem : α) (fallback : β)
    (uniform : ∀ x ∈ items, (f x).length = width)
    (block offset : Nat) (blockBound : block < items.length) (offsetBound : offset < width) :
    (items.flatMap f).getD (block * width + offset) fallback =
      (f (items.getD block fallbackItem)).getD offset fallback := by
  induction items generalizing block with
  | nil => simp at blockBound
  | cons head tail ih =>
      have headWidth := uniform head (by simp)
      have tailWidth : ∀ x ∈ tail, (f x).length = width := by
        intro x member
        exact uniform x (by simp [member])
      cases block with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add, List.getD_cons_zero, List.flatMap_cons]
          exact List.getD_append _ _ _ _ (by omega)
      | succ block =>
          rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by
            rw [headWidth]
            simp only [Nat.succ_mul]
            omega)]
          rw [headWidth, show (block + 1) * width + offset - width =
            block * width + offset by
              simp only [Nat.add_mul, Nat.one_mul]
              omega]
          simpa only [List.getD_cons_succ] using
            ih tailWidth block (by simpa using blockBound)

theorem uniform_flatMap_getD {α β : Type*} (items : List α) (f : α → List β)
    (width : Nat) (fallbackItem : α) (fallback : β) (positive : 0 < width)
    (uniform : ∀ x ∈ items, (f x).length = width)
    (index : Nat) (bounded : index < items.length * width) :
    (items.flatMap f).getD index fallback =
      (f (items.getD (index / width) fallbackItem)).getD (index % width) fallback := by
  have blockBound : index / width < items.length :=
    (Nat.div_lt_iff_lt_mul positive).mpr bounded
  have offsetBound := Nat.mod_lt index positive
  have partition : index / width * width + index % width = index :=
    Nat.div_add_mod' index width
  simpa only [partition] using uniform_flatMap_block items f width fallbackItem fallback
    uniform (index / width) (index % width) blockBound offsetBound

theorem uniform_range_getD {β : Type*} (first count width : Nat) (f : Nat → List β)
    (fallback : β) (positive : 0 < width)
    (uniform : ∀ x ∈ List.range' first count, (f x).length = width)
    (index : Nat) (bounded : index < count * width) :
    ((List.range' first count).flatMap f).getD index fallback =
      (f (first + index / width)).getD (index % width) fallback := by
  have blockBound : index / width < count := (Nat.div_lt_iff_lt_mul positive).mpr bounded
  rw [uniform_flatMap_getD _ f width first fallback positive uniform index (by simpa using bounded)]
  have selected : (List.range' first count).getD (index / width) first =
      first + index / width := by
    rw [List.getD_eq_getElem _ _ (by simpa using blockBound)]
    simp
  rw [selected]

end ProjectEulerStatements.UniformBlocks
