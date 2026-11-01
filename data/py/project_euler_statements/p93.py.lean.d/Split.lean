import data.«project-euler-statements».data.py.project_euler_statements.«p93.py.lean.d».RecursiveCalls

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
open ProjectEulerSolutions.HeapCollection
set_option Elab.async false

structure Ready (env : HeapCalls.Env) (input collector : Nat) : Prop where
  nums : env "nums" = some (.ref input)
  out : env "out" = some (.ref collector)

abbrev atSplit (xs : List Int) (split : Nat) : List Pair :=
  combine (enumeratePairs (xs.take split)) (enumeratePairs (xs.drop split))

/-- Recursive calls preserve the collector while the two child lists are built. -/
theorem split_result (xs : List Int) (smaller : Smaller xs) (base : Mutable.Heap) (input split : Nat)
    (source : base[input]? = some (.tuple (integers xs))) (positive : 0 < split) (proper : split < xs.length)
    (old : List Mutable.Value) (garbage : Mutable.Heap) (pairs : List Pair)
    (env : HeapCalls.Env) (globals : Mutable.Globals)
    (rows : Heap.Rows (working base old garbage) old pairs) (ready : Ready env input base.length)
    (getSplit : env "split" = some (Heap.number split)) :
    ∃ appended extra finalEnv,
      BlockContinues program env splitBody (working base old garbage) finalEnv
        (working base (old ++ appended) (garbage ++ extra)) globals ∧
      Heap.Rows (working base (old ++ appended) (garbage ++ extra))
        (old ++ appended) (pairs ++ atSplit xs split) ∧ Ready finalEnv input base.length := by
  obtain ⟨left, leftExtra, freshLeft, calledLeft, leftFound⟩ :=
    prefix_call xs smaller (working base old garbage) input split env globals
      (prefix_found base (.list old :: garbage) input _ source) proper ready.nums getSplit
  let afterLeft := setLocal env "left" (.ref left)
  have sourceLeft : (working base old garbage ++ leftExtra)[input]? = some (.tuple (integers xs)) :=
    prefix_found (working base old garbage) leftExtra input _
      (prefix_found base (.list old :: garbage) input _ source)
  obtain ⟨right, rightExtra, freshRight, calledRight, rightFound⟩ :=
    suffix_call xs smaller (working base old garbage ++ leftExtra) input split afterLeft globals
      sourceLeft positive proper (by simpa [afterLeft, setLocal] using ready.nums)
      (by simpa [afterLeft, setLocal] using getSplit)
  let afterRight := setLocal afterLeft "right" (.ref right)
  let temporary := leftExtra ++ rightExtra
  have currentLeft : Heap.ListFound (working base old (garbage ++ temporary)) left (enumeratePairs (xs.take split)) := by
    simpa only [temporary, append, List.append_assoc] using leftFound.append rightExtra
  have currentRight : Heap.ListFound (working base old (garbage ++ temporary)) right (enumeratePairs (xs.drop split)) := by
    simpa only [temporary, append, List.append_assoc] using rightFound
  have currentRows : Heap.Rows (working base old (garbage ++ temporary)) old pairs := by
    simpa only [append] using rows.append temporary
  have differentLeft : base.length ≠ left := by
    simp only [working, List.length_append, List.length_cons] at freshLeft
    omega
  have differentRight : base.length ≠ right := by
    simp only [working, List.length_append, List.length_cons] at freshRight
    omega
  obtain ⟨leftValues, foundLeft, leftRows⟩ := currentLeft
  obtain ⟨rightValues, foundRight, rightRows⟩ := currentRight
  obtain ⟨appended, extra, finalEnv, collected, finalRows, kept⟩ :=
    outer base left right leftValues rightValues (enumeratePairs (xs.drop split)) differentLeft differentRight
      (enumeratePairs (xs.take split)) leftValues 0 old (garbage ++ temporary) pairs afterRight globals
      foundLeft foundRight rfl currentRows leftRows rightRows
      (by simpa [afterRight, afterLeft, setLocal] using ready.out) (by simp [afterRight, setLocal])
  have loop : BlockContinues program afterRight [.forIn (.name "a") (.name "left") innerBody []]
      (working base old (garbage ++ temporary)) finalEnv
      (working base (old ++ appended) ((garbage ++ temporary) ++ extra)) globals := by
    apply BlockContinues.for_sequence (items := leftValues) (value := .ref left)
      (by intro expressions impossible; cases impossible)
      (Evaluates.lookup (by simp [afterRight, afterLeft, setLocal]))
      (by simp [Mutable.sequence, foundLeft])
    exact collected
  have rightAssignment := BlockContinues.assign (name := "right") calledRight
  have leftAssignment := BlockContinues.assign (name := "left") calledLeft
  have normalizedRight : BlockContinues program afterLeft
      [.assign [.name "right"] (.call (.name "all_results")
        [.subscript (.name "nums") (.slice (some (.name "split")) none none)])]
      (working base old garbage ++ leftExtra) afterRight (working base old (garbage ++ temporary)) globals := by
    simpa only [afterRight, temporary, append, List.append_assoc] using rightAssignment
  refine ⟨appended, temporary ++ extra, finalEnv, ?_, ?_, ?_⟩
  · simpa only [splitBody, List.singleton_append, List.append_assoc] using
      leftAssignment.append (normalizedRight.append loop)
  · simpa only [List.append_assoc] using finalRows
  · constructor
    · rw [kept "nums" (by decide) (by decide)]
      simpa [afterRight, afterLeft, setLocal] using ready.nums
    · rw [kept "out" (by decide) (by decide)]
      simpa [afterRight, afterLeft, setLocal] using ready.out

end data.«project-euler-statements».data.py.project_euler_statements.p93.all_results
