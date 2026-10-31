import data.«project-euler-statements».data.py.project_euler_statements.«p88.py.lean.d».Preparation
import ProjectEulerSolutions.Lib.ProductSumDistinct

namespace data.«project-euler-statements».data.py.project_euler_statements.p88.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.ProductSumNumbers
set_option Elab.async false

/-- A Boolean table represents precisely the values already included in the sum. -/
def flags (limit : Nat) (visited : Finset Nat) : List Mutable.Value :=
  (List.range (limit + 1)).map (fun value => .scalar (.bool (decide (value ∈ visited))))

def scanHeap (base : Mutable.Heap) (limit : Nat) (visited : Finset Nat) : Mutable.Heap :=
  base ++ [.list (flags limit visited)]

@[simp] theorem flags_length (limit : Nat) (visited : Finset Nat) :
    (flags limit visited).length = limit + 1 := by simp [flags]

theorem flags_empty (limit : Nat) :
    flags limit ∅ = List.replicate (limit + 1) (.scalar (.bool false)) := by
  simp [flags, List.map_const']

theorem flags_lookup (limit value : Nat) (visited : Finset Nat) (inside : value ≤ limit) :
    (flags limit visited)[value]? = some (.scalar (.bool (decide (value ∈ visited)))) := by
  simp [flags, show value < limit + 1 by omega]

theorem flags_insert (limit value : Nat) (visited : Finset Nat) (inside : value ≤ limit) :
    (flags limit visited).set value (.scalar (.bool true)) = flags limit (insert value visited) := by
  apply List.ext_getElem?
  intro index
  by_cases bound : index < limit + 1
  · by_cases same : value = index
    · subst index
      rw [List.getElem?_set_self (by simpa using bound), flags_lookup limit value _ inside]
      simp
    · rw [List.getElem?_set_ne same, flags_lookup limit index _ (by omega),
        flags_lookup limit index _ (by omega)]
      simp [Ne.symm same]
  · rw [List.getElem?_eq_none_iff.mpr (by simp; omega),
      List.getElem?_eq_none_iff.mpr (by simp; omega)]

theorem scanHeap_found (base : Mutable.Heap) (limit : Nat) (visited : Finset Nat) :
    (scanHeap base limit visited)[base.length]? = some (.list (flags limit visited)) := by
  simp [scanHeap]

theorem scanHeap_prefix (base : Mutable.Heap) (limit : Nat) (visited : Finset Nat)
    (address : Nat) (object : Mutable.Object) (found : base[address]? = some object) :
    (scanHeap base limit visited)[address]? = some object := by
  have inside : address < base.length := List.getElem?_eq_some_iff.mp found |>.1
  simpa [scanHeap, List.getElem?_append, inside] using found

structure ScanLocals (env : HeapCalls.Env) (limit tableAddress seenAddress : Nat)
    (visited : Finset Nat) : Prop where
  bound : env "limit" = some (number limit)
  best : env "best" = some (.ref tableAddress)
  seen : env "seen" = some (.ref seenAddress)
  total : env "total" = some (number (visited.sum id))

abbrev scanBody : List Stmt := match code[6]'(by decide) with
  | .forIn _ _ body _ => body
  | _ => []

def valueEnv (env : HeapCalls.Env) (value : Nat) : HeapCalls.Env :=
  setLocal env "v" (number value)

def collectedEnv (env : HeapCalls.Env) (value : Nat) (visited : Finset Nat) : HeapCalls.Env :=
  if value ∈ visited then valueEnv env value
  else setLocal (valueEnv env value) "total" (number ((insert value visited).sum id))

theorem ScanLocals.collected {env : HeapCalls.Env} {limit tableAddress seenAddress : Nat}
    {visited : Finset Nat} (ready : ScanLocals env limit tableAddress seenAddress visited) (value : Nat) :
    ScanLocals (collectedEnv env value visited) limit tableAddress seenAddress (insert value visited) := by
  rcases ready with ⟨bound, best, seen, total⟩
  by_cases member : value ∈ visited
  · simp only [collectedEnv, if_pos member, Finset.insert_eq_of_mem member]
    exact ⟨by simpa [valueEnv, setLocal] using bound,
      by simpa [valueEnv, setLocal] using best, by simpa [valueEnv, setLocal] using seen,
      by simpa [valueEnv, setLocal] using total⟩
  · simp only [collectedEnv, if_neg member]
    exact ⟨by simpa [valueEnv, setLocal] using bound,
      by simpa [valueEnv, setLocal] using best, by simpa [valueEnv, setLocal] using seen,
      by simp [setLocal]⟩

end data.«project-euler-statements».data.py.project_euler_statements.p88.naive
