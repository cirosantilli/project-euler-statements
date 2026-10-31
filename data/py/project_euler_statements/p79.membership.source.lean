import data.«project-euler-statements».data.py.project_euler_statements.«p79.edges.source»

/-! Reference duplicate removal compares contents, including separately allocated edge tuples. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p79
open FormalSW.PyAst HeapCalls
set_option Elab.async false

theorem sequence_contains_by {α β : Type} [DecidableEq β] (heap : Mutable.Heap)
    (encode : α → Mutable.Value) (key : α → β) (items : List α) (needle : α)
    (identity : ∀ item ∈ items, encode item = encode needle → key item = key needle)
    (compared : ∀ item ∈ items, HeapCalls.compare .eq (encode item) (encode needle) heap =
      some (.ok (.scalar (.bool (decide (key item = key needle)))), heap)) :
    sequenceContains (encode needle) (items.map encode) heap =
      some (.ok (decide (key needle ∈ items.map key)), heap) := by
  induction items with
  | nil => simp [sequenceContains]
  | cons item rest ih =>
      have restResult := ih (fun other member => identity other (by simp [member]))
        (fun other member => compared other (by simp [member]))
      by_cases sameValue : encode item = encode needle
      · have sameKey := identity item (by simp) sameValue
        simp [sequenceContains, sameValue, sameKey]
      · have tested := compared item (by simp)
        by_cases sameKey : key item = key needle
        · simp [sequenceContains, sameValue, tested, sameKey, Mutable.truth, scalarTruth]
        · simp [sequenceContains, sameValue, tested, sameKey, Ne.symm sameKey,
            Mutable.truth, scalarTruth, restResult]

theorem list_membership_by {α β : Type} [DecidableEq β] (heap : Mutable.Heap) (address : Nat)
    (encode : α → Mutable.Value) (key : α → β) (items : List α) (needle : α)
    (found : heap[address]? = some (.list (items.map encode)))
    (identity : ∀ item ∈ items, encode item = encode needle → key item = key needle)
    (compared : ∀ item ∈ items, HeapCalls.compare .eq (encode item) (encode needle) heap =
      some (.ok (.scalar (.bool (decide (key item = key needle)))), heap)) :
    membership (encode needle) (.ref address) true heap =
      some (.ok (.scalar (.bool (decide (key needle ∉ items.map key)))), heap) := by
  simp [membership, found, sequence_contains_by heap encode key items needle identity compared,
    Except.map, -List.mem_map]

theorem strings_membership (heap : Mutable.Heap) (address : Nat) (items : List String)
    (needle : String) (found : heap[address]? = some (.list (items.map text))) :
    membership (text needle) (.ref address) true heap =
      some (.ok (.scalar (.bool (decide (needle ∉ items)))), heap) := by
  simpa using list_membership_by heap address text id items needle found
    (by intro item _ same; simpa using same)
    (by intro item _; simp [HeapCalls.compare, scalarCompare])

theorem edge_identity (heap : Mutable.Heap) (left right : Edge)
    (storedLeft : Stored heap left) (storedRight : Stored heap right)
    (same : edgeValue left = edgeValue right) : left.2 = right.2 := by
  have addresses : left.1 = right.1 := by simpa using same
  change heap[left.1]? = _ at storedLeft
  change heap[right.1]? = _ at storedRight
  rw [addresses, storedRight] at storedLeft
  simp only [Option.some.injEq, Mutable.Object.tuple.injEq, List.cons.injEq,
    Mutable.Value.scalar.injEq, Constant.string.injEq, and_true] at storedLeft
  exact Prod.ext storedLeft.1.symm storedLeft.2.symm

theorem edge_compare (heap : Mutable.Heap) (left right : Edge)
    (storedLeft : Stored heap left) (storedRight : Stored heap right) :
    HeapCalls.compare .eq (edgeValue left) (edgeValue right) heap =
      some (.ok (.scalar (.bool (decide (left.2 = right.2)))), heap) := by
  have leftFound := storedLeft
  have rightFound := storedRight
  change heap[left.1]? = _ at leftFound
  change heap[right.1]? = _ at rightFound
  by_cases sameAddress : left.1 = right.1
  · have same := edge_identity heap left right storedLeft storedRight (by simp [sameAddress])
    simp [HeapCalls.compare, rightFound, sameAddress, same]
    rfl
  · by_cases first : left.2.1 = right.2.1 <;>
      by_cases second : left.2.2 = right.2.2 <;>
        simp [HeapCalls.compare, leftFound, rightFound, sameAddress, equalLists, equalElements,
          scalarCompare, first, second, Prod.ext_iff] <;> rfl

theorem edges_membership (heap : Mutable.Heap) (address : Nat) (entries : List Edge)
    (needle : Edge) (found : heap[address]? = some (.list (entries.map edgeValue)))
    (stored : ∀ entry ∈ entries, Stored heap entry) (needleStored : Stored heap needle) :
    membership (edgeValue needle) (.ref address) true heap =
      some (.ok (.scalar (.bool (decide (needle.2 ∉ entries.map Prod.snd)))), heap) := by
  simpa using list_membership_by heap address edgeValue Prod.snd entries needle found
    (fun entry member => edge_identity heap entry needle (stored entry member) needleStored)
    (fun entry member => edge_compare heap entry needle (stored entry member) needleStored)

end data.«project-euler-statements».data.py.project_euler_statements.p79
