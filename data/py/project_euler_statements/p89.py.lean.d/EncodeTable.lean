import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».EncodeSigned

namespace data.«project-euler-statements».data.py.project_euler_statements.p89.int_to_roman_aux
open FormalSW.PyAst HeapCalls ProjectEulerSolutions RomanNumerals
set_option Elab.async false

structure Entry where
  denomination : Nat
  token : List Mutable.Value
  pairAddress : Nat
  tokenAddress : Nat

def Entry.model (entry : Entry) : Nat × List Mutable.Value := (entry.denomination, entry.token)
def Entry.reference (entry : Entry) : Mutable.Value := .ref entry.pairAddress

structure Entry.Valid (base : Mutable.Heap) (entry : Entry) : Prop where
  positive : 0 < entry.denomination
  pair : base[entry.pairAddress]? = some (.tuple [number entry.denomination, .ref entry.tokenAddress])
  token : base[entry.tokenAddress]? = some (.list entry.token)

/-- The table iterator reads each existing tuple and runs its complete subtraction loop. -/
theorem table_loop (base : Mutable.Heap) (tableAddress : Nat) (entries remaining : List Entry)
    (found : base[tableAddress]? = some (.list (entries.map Entry.reference)))
    (valid : ∀ entry ∈ remaining, entry.Valid base) (position : Nat)
    (suffix : entries.drop position = remaining) (n : Int) (output : List Mutable.Value)
    (env : HeapCalls.Env) (getN : env "n" = some (.scalar (.int n)))
    (getOut : env "out" = some (.ref base.length)) :
    ∃ finalEnv,
      BlockContinues program env [.unpackStepLoop ["v", "cs"] (.ref tableAddress) position loopCode []]
        (HeapCollection.working base output []) finalEnv
        (HeapCollection.working base (output ++ encode (remaining.map Entry.model) n.toNat) []) ∧
      finalEnv "out" = some (.ref base.length) := by
  induction remaining generalizing position n output env with
  | nil =>
      have done : entries[position]? = none := List.getElem?_eq_none_iff.mpr (List.drop_eq_nil_iff.mp suffix)
      refine ⟨env, ?_, getOut⟩
      simp only [List.map_nil, encode, List.append_nil]
      apply BlockContinues.unpack_done (items := entries.map Entry.reference)
      · have table := HeapCollection.prefix_found base [.list output] tableAddress _ found
        simp [sequenceValue, Mutable.sequence, HeapCollection.working, table]
      · simp [done]
      · exact .nil
  | cons entry rest ih =>
      have current := valid entry (by simp)
      have item : entries[position]? = some entry := by
        have head := congrArg (fun xs : List Entry => xs[0]?) suffix
        simpa using head
      have tail : entries.drop (position + 1) = rest := by
        have dropped := congrArg (List.drop 1) suffix
        simpa [List.drop_drop, Nat.add_comm] using dropped
      let bound := assignNames env ["v", "cs"] [number entry.denomination, .ref entry.tokenAddress]
      obtain ⟨afterLoop, remainder, iterated, nextN, nextNat, nextOut, _⟩ :=
        repeat_signed entry.denomination current.positive entry.token entry.tokenAddress base current.token n output bound
          (by simpa [bound, assignNames, setLocal] using getN)
          (by simp [bound, assignNames, setLocal]) (by simp [bound, assignNames, setLocal])
          (by simpa [bound, assignNames, setLocal] using getOut)
      obtain ⟨finalEnv, continued, finalOut⟩ := ih (fun e mem => valid e (by simp [mem]))
        (position + 1) tail remainder (output ++ copies entry.token (n.toNat / entry.denomination)) afterLoop nextN nextOut
      refine ⟨finalEnv, ?_, finalOut⟩
      simp only [List.map_cons, Entry.model, encode, ← List.append_assoc, ← nextNat]
      apply BlockContinues.unpack_step (items := entries.map Entry.reference)
        (value := .ref entry.pairAddress) (values := [number entry.denomination, .ref entry.tokenAddress])
      · have table := HeapCollection.prefix_found base [.list output] tableAddress _ found
        simp [sequenceValue, Mutable.sequence, HeapCollection.working, table]
      · simp [item, Entry.reference]
      · have pair := HeapCollection.prefix_found base [.list output] entry.pairAddress _ current.pair
        simp [Mutable.sequence, HeapCollection.working, pair]
      · rfl
      · simpa only [Calls.loopContinuation, show Calls.loopControl loopCode = false from rfl, if_false] using
          iterated.append continued

/-- The source for-loop produces the generic greedy encoding for all signed inputs. -/
theorem table_result (base : Mutable.Heap) (tableAddress : Nat) (entries : List Entry)
    (found : base[tableAddress]? = some (.list (entries.map Entry.reference)))
    (valid : ∀ entry ∈ entries, entry.Valid base) (n : Int) (output : List Mutable.Value)
    (env : HeapCalls.Env) (getN : env "n" = some (.scalar (.int n)))
    (getOut : env "out" = some (.ref base.length)) (getTable : env "table" = some (.ref tableAddress)) :
    ∃ finalEnv,
      BlockContinues program env [code[2]'(by decide)] (HeapCollection.working base output []) finalEnv
        (HeapCollection.working base (output ++ encode (entries.map Entry.model) n.toNat) []) ∧
      finalEnv "out" = some (.ref base.length) := by
  obtain ⟨finalEnv, ran, finalOut⟩ := table_loop base tableAddress entries entries found valid 0 rfl n output env getN getOut
  refine ⟨finalEnv, ?_, finalOut⟩
  apply BlockContinues.for_unpack (items := entries.map Entry.reference)
    (middle := HeapCollection.working base output []) (by intros; simp) rfl (Evaluates.lookup getTable)
  · have table := HeapCollection.prefix_found base [.list output] tableAddress _ found
    simp [Mutable.sequence, HeapCollection.working, table]
  · exact ran

end data.«project-euler-statements».data.py.project_euler_statements.p89.int_to_roman_aux
