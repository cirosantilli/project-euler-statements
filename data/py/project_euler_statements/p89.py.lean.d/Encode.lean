import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».EncodeAllocation
import ProjectEulerSolutions.Lib.RomanEncoding

namespace data.«project-euler-statements».data.py.project_euler_statements.p89.int_to_roman_aux
open FormalSW.PyAst HeapCalls ProjectEulerSolutions RomanNumerals
set_option Elab.async false
variable {globals : Mutable.Globals}

def outputValues (n : Nat) : List Mutable.Value := (canonical n).map (fun c => string (String.singleton c))

theorem raw_encoding (n : Nat) : encode (rawTokens.map rawModel) n = outputValues n := by
  simpa [rawTokens, rawModel, outputValues, canonical, List.map_map, Function.comp_def] using
    encode_map (fun c => string (String.singleton c)) (tokens.map (fun pair => (pair.1, pair.2.toList))) n

/-- Complete reference encoding, including the literal table, output allocation, and every token loop. -/
theorem result (n : Int) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue (globals := globals) program "int_to_roman_aux" [.scalar (.int n)] heap (.ref (heap ++ extra).length)
      ((heap ++ extra) ++ [.list (outputValues n.toNat)]) := by
  let entry := functionEnv ((findFunctionIn program.body "int_to_roman_aux").getD ([], [])).1
    ((findFunctionIn program.body "int_to_roman_aux").getD ([], [])).2 [.scalar (.int n)] globals
  have getN : entry "n" = some (.scalar (.int n)) := by cases globals <;> rfl
  obtain ⟨extra, entries, allocated, valid, models⟩ := allocate_table (globals := globals) heap entry
  let base := (heap ++ extra) ++ [.list (entries.map Entry.reference)]
  let withTable := setLocal entry "table" (.ref (heap ++ extra).length)
  let ready := setLocal withTable "out" (.ref base.length)
  have assigned : BlockContinues (globals := globals) program entry [code[0]'(by decide)] heap withTable base :=
    BlockContinues.assign allocated
  have outputAllocated : BlockContinues (globals := globals) program withTable [code[1]'(by decide)] base ready
      (HeapCollection.working base [] []) :=
    BlockContinues.assign (Evaluates.list .nil)
  have found : base[(heap ++ extra).length]? = some (.list (entries.map Entry.reference)) := by simp [base]
  obtain ⟨finalEnv, scanned, finalOut⟩ := table_result (globals := globals) base (heap ++ extra).length entries found valid n [] ready
    (by simpa [ready, withTable, setLocal] using getN) (by simp [ready, setLocal])
    (by simp [ready, withTable, setLocal])
  have modeled : encode (entries.map Entry.model) n.toNat = outputValues n.toNat := by rw [models, raw_encoding]
  have returned : ReturnsValue (globals := globals) program "int_to_roman_aux" [.scalar (.int n)] heap (.ref base.length)
      (HeapCollection.working base (outputValues n.toNat) []) := by
    apply BlockReturns.function rfl rfl
    apply assigned.returns
    apply outputAllocated.returns
    have scan : BlockContinues (globals := globals) program ready [code[2]'(by decide)] (HeapCollection.working base [] []) finalEnv
        (HeapCollection.working base (outputValues n.toNat) []) := by simpa only [modeled, List.nil_append] using scanned
    apply scan.returns
    exact BlockReturns.return_value (Evaluates.lookup finalOut)
  refine ⟨extra ++ [.list (entries.map Entry.reference)], ?_⟩
  simpa only [base, HeapCollection.working, List.append_assoc] using returned

end data.«project-euler-statements».data.py.project_euler_statements.p89.int_to_roman_aux
