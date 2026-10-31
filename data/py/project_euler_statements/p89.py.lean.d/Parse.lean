import data.«project-euler-statements».data.py.project_euler_statements.«p89.py.lean.d».ParseState

namespace data.«project-euler-statements».data.py.project_euler_statements.p89.roman_to_int
open FormalSW.PyAst HeapCalls ProjectEulerSolutions
set_option Elab.async false

/-- Recursive parsing follows the shrinking input list and preserves all pre-existing objects. -/
theorem result (input : List String) (heap : Mutable.Heap) (address : Nat)
    (found : heap[address]? = some (.list (encode input))) :
    ∃ extra, ReturnsValue program "roman_to_int" [.ref address] heap (number (RomanNumerals.parse input))
      (heap ++ extra) := by
  let entry := functionEnv ((findFunctionIn program.body "roman_to_int").getD ([], [])).1
    ((findFunctionIn program.body "roman_to_int").getD ([], [])).2 [.ref address] []
  have getInput : entry "chars" = some (.ref address) := rfl
  cases input with
  | nil =>
      refine ⟨[], ?_⟩
      simp only [List.append_nil]
      apply BlockReturns.function rfl rfl
      apply BlockReturns.branch (flag := true) (empty_test [] heap address found entry getInput) rfl
      exact BlockReturns.return_value Evaluates.constant
  | cons first rest =>
      have nonempty : BlockContinues program entry [code[0]'(by decide)] heap entry heap :=
        BlockContinues.branch (flag := false) (empty_test (first :: rest) heap address found entry getInput) rfl .nil
      cases rest with
      | nil =>
          refine ⟨[.dict valueEntries], ?_⟩
          apply BlockReturns.function rfl rfl
          apply nonempty.returns
          apply BlockReturns.branch (flag := true) (length_test [first] heap address found entry getInput) rfl
          exact BlockReturns.return_value (value_call first _ heap entry
            (read [first] 0 (by simp) heap address found entry getInput))
      | cons second rest =>
          let pairHeap := heap ++ [.tuple [string first, string second]]
          let paired := pairEnv entry first second
          let compared := pairHeap ++ [.dict valueEntries, .dict valueEntries]
          have pairedInput : paired "chars" = some (.ref address) := by
            simpa [paired, pairEnv, assignNames, setLocal] using getInput
          have pairedFirst : paired "a" = some (string first) := by simp [paired, pairEnv, assignNames, setLocal]
          have pairedSecond : paired "b" = some (string second) := by simp [paired, pairEnv, assignNames, setLocal]
          have notSingle : BlockContinues program entry [code[1]'(by decide)] heap entry heap :=
            BlockContinues.branch (flag := false) (length_test (first :: second :: rest) heap address found entry getInput)
              (by simp [Mutable.truth, scalarTruth]) .nil
          have unpacked := unpack_pair first second rest heap address found entry getInput
          have tested := comparison first second pairHeap paired pairedFirst pairedSecond
          by_cases subtract : RomanNumerals.value first < RomanNumerals.value second
          · let leftHeap := compared ++ [.dict valueEntries, .dict valueEntries]
            let slicedHeap := leftHeap ++ [.list (encode rest)]
            have kept : leftHeap[address]? = some (.list (encode (first :: second :: rest))) := by
              simp only [leftHeap, compared, pairHeap, List.append_assoc]
              exact HeapCollection.prefix_found heap _ address _ found
            obtain ⟨extra, recursive⟩ := result rest slicedHeap leftHeap.length (by simp [slicedHeap])
            refine ⟨[.tuple [string first, string second], .dict valueEntries, .dict valueEntries,
              .dict valueEntries, .dict valueEntries, .list (encode rest)] ++ extra, ?_⟩
            have final : heap ++ ([.tuple [string first, string second], .dict valueEntries, .dict valueEntries,
                .dict valueEntries, .dict valueEntries, .list (encode rest)] ++ extra) = slicedHeap ++ extra := by
              simp [slicedHeap, leftHeap, compared, pairHeap, List.append_assoc]
            rw [final]
            apply BlockReturns.function rfl rfl
            apply nonempty.returns
            apply notSingle.returns
            apply unpacked.returns
            apply BlockReturns.branch (flag := true) tested (by simp [Mutable.truth, scalarTruth, subtract])
            apply BlockReturns.return_value
            apply Evaluates.binary (av := number (RomanNumerals.value second - RomanNumerals.value first))
              (bv := number (RomanNumerals.parse rest)) (middle := leftHeap) (afterRight := slicedHeap ++ extra)
            · apply Evaluates.binary
                (av := number (RomanNumerals.value second)) (bv := number (RomanNumerals.value first))
                (middle := compared ++ [.dict valueEntries])
                (afterRight := (compared ++ [.dict valueEntries]) ++ [.dict valueEntries])
              · exact value_call second _ compared paired (Evaluates.lookup pairedSecond)
              · exact value_call first _ (compared ++ [.dict valueEntries]) paired (Evaluates.lookup pairedFirst)
              · simp [Mutable.binary, scalarBinary, number, Nat.cast_sub (Nat.le_of_lt subtract),
                  leftHeap, List.append_assoc]
            · apply Evaluates.call (values := [.ref leftHeap.length]) (middle := slicedHeap)
              · exact .cons (slice (first :: second :: rest) 2 leftHeap address kept paired pairedInput) .nil
              · exact recursive
            · simp [Mutable.binary, scalarBinary, number, RomanNumerals.parse, subtract]
          · let leftHeap := compared ++ [.dict valueEntries]
            let slicedHeap := leftHeap ++ [.list (encode (second :: rest))]
            have kept : leftHeap[address]? = some (.list (encode (first :: second :: rest))) := by
              simp only [leftHeap, compared, pairHeap, List.append_assoc]
              exact HeapCollection.prefix_found heap _ address _ found
            obtain ⟨extra, recursive⟩ := result (second :: rest) slicedHeap leftHeap.length (by simp [slicedHeap])
            refine ⟨[.tuple [string first, string second], .dict valueEntries, .dict valueEntries,
              .dict valueEntries, .list (encode (second :: rest))] ++ extra, ?_⟩
            have final : heap ++ ([.tuple [string first, string second], .dict valueEntries, .dict valueEntries,
                .dict valueEntries, .list (encode (second :: rest))] ++ extra) = slicedHeap ++ extra := by
              simp [slicedHeap, leftHeap, compared, pairHeap, List.append_assoc]
            rw [final]
            apply BlockReturns.function rfl rfl
            apply nonempty.returns
            apply notSingle.returns
            apply unpacked.returns
            apply BlockReturns.branch (flag := false) tested (by simp [Mutable.truth, scalarTruth, subtract])
            apply BlockReturns.return_value
            apply Evaluates.binary (av := number (RomanNumerals.value first))
              (bv := number (RomanNumerals.parse (second :: rest))) (middle := leftHeap) (afterRight := slicedHeap ++ extra)
            · exact value_call first _ compared paired (Evaluates.lookup pairedFirst)
            · apply Evaluates.call (values := [.ref leftHeap.length]) (middle := slicedHeap)
              · exact .cons (slice (first :: second :: rest) 1 leftHeap address kept paired pairedInput) .nil
              · exact recursive
            · simp [Mutable.binary, scalarBinary, number, RomanNumerals.parse, subtract]
termination_by input.length

end data.«project-euler-statements».data.py.project_euler_statements.p89.roman_to_int
