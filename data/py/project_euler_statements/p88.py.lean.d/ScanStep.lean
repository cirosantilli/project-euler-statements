import data.«project-euler-statements».data.py.project_euler_statements.«p88.py.lean.d».ScanState

namespace data.«project-euler-statements».data.py.project_euler_statements.p88.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.ProductSumNumbers
set_option Elab.async false

/-- Each reference iteration adds precisely a previously unseen bounded value. -/
theorem scan_step (limit index value tableAddress : Nat) (best : List Nat)
    (lookup : best[index]? = some value) (bounded : value ≤ limit)
    (base : Mutable.Heap) (found : base[tableAddress]? = some (.list (encode best)))
    (visited : Finset Nat) (env : HeapCalls.Env)
    (ready : ScanLocals env limit tableAddress base.length visited)
    (getIndex : env "k" = some (number index)) :
    BlockContinues program env scanBody (scanHeap base limit visited)
      (collectedEnv env value visited) (scanHeap base limit (insert value visited)) := by
  let heap := scanHeap base limit visited
  let measured := valueEnv env value
  have inside : index < best.length := (List.getElem?_eq_some_iff.mp lookup).1
  have selected : Evaluates program env (.subscript (.name "best") (.name "k")) heap (number value) heap := by
    apply Evaluates.subscript (by intros; simp) (Evaluates.lookup ready.best) (Evaluates.lookup getIndex)
    have read := Mutable.getItem_list heap tableAddress index (encode best)
      (scanHeap_prefix base limit visited tableAddress _ found) (by simpa using inside)
    have actual : best[index] = value := (List.getElem?_eq_some_iff.mp lookup).2
    simpa [encode, actual] using read
  have assigned : BlockContinues program env [scanBody[0]'(by decide)] heap measured heap :=
    BlockContinues.assign selected
  have atMost : Evaluates program measured (.compare (.name "v") [(.ltE, .name "limit")]) heap
      (.scalar (.bool true)) heap := by
    apply Evaluates.compare (av := number value) (bv := number limit) (Evaluates.lookup (by simp [measured, valueEnv, setLocal]))
      (Evaluates.lookup (by simpa [measured, valueEnv, setLocal] using ready.bound))
    simp [HeapCalls.compare, scalarCompare, evalCmpOp, bounded]
  have seen : Evaluates program measured (.subscript (.name "seen") (.name "v")) heap
      (.scalar (.bool (decide (value ∈ visited)))) heap := by
    apply Evaluates.subscript (value := .ref base.length) (position := number value) (by intros; simp)
      (Evaluates.lookup (by simpa [measured, valueEnv, setLocal] using ready.seen))
      (Evaluates.lookup (by simp [measured, valueEnv, setLocal]))
    have read := Mutable.getItem_list heap base.length value (flags limit visited)
      (scanHeap_found base limit visited) (by simp; omega)
    have actual := (List.getElem?_eq_some_iff.mp (flags_lookup limit value visited bounded)).2
    simpa only [actual] using read
  have unseen : Evaluates program measured (.unaryOp .not (.subscript (.name "seen") (.name "v"))) heap
      (.scalar (.bool (decide (value ∉ visited)))) heap := by
    apply Evaluates.unary seen
    by_cases member : value ∈ visited <;> simp [HeapCalls.unary, Mutable.truth, scalarTruth, member]
  have tested : Evaluates program measured
      (.boolOp .and [.compare (.name "v") [(.ltE, .name "limit")],
        .unaryOp .not (.subscript (.name "seen") (.name "v"))]) heap
      (.scalar (.bool (decide (value ∉ visited)))) heap := by
    apply Evaluates.boolean_next (flag := true) atMost rfl rfl
    exact Evaluates.boolean_last (flag := decide (value ∉ visited)) unseen (by simp [Mutable.truth, scalarTruth])
  apply assigned.append
  by_cases member : value ∈ visited
  · simpa only [collectedEnv, if_pos member, Finset.insert_eq_of_mem member] using
      (BlockContinues.branch (flag := false) tested (by simp [Mutable.truth, scalarTruth, member]) .nil :
        BlockContinues program measured [scanBody[1]'(by decide)] heap measured heap)
  · have stored : BlockContinues program measured
        [.assign [.subscript (.name "seen") (.name "v")] (.constant (.bool true))]
        heap measured (scanHeap base limit (insert value visited)) := by
      apply BlockContinues.setItem (value := .scalar (.bool true)) (receiver := .ref base.length)
        (subscript := number value) (by intros; simp) Evaluates.constant
        (.cons (Evaluates.lookup (by simpa [measured, valueEnv, setLocal] using ready.seen))
          (.cons (Evaluates.lookup (by simp [measured, valueEnv, setLocal])) .nil))
      simpa [heap, scanHeap, List.set_append_right, flags_insert limit value visited bounded] using
        ProjectEulerSolutions.HeapTables.setItem_list heap base.length value (flags limit visited)
          (.scalar (.bool true)) (scanHeap_found base limit visited) (by simp; omega)
    have added : BlockContinues program measured [.augAssign (.name "total") .add (.name "v")]
        (scanHeap base limit (insert value visited)) (collectedEnv env value visited)
        (scanHeap base limit (insert value visited)) := by
      simp only [collectedEnv, if_neg member]
      apply BlockContinues.augAssign (left := number (visited.sum id)) (right := number value)
        (by simpa [measured, valueEnv, setLocal] using ready.total)
        (Evaluates.lookup (by simp [measured, valueEnv, setLocal]))
      simp [inplace, Mutable.binary, scalarBinary, number, Finset.sum_insert member, Int.add_comm]
    exact BlockContinues.branch (flag := true) tested (by simp [Mutable.truth, scalarTruth, member])
      (stored.append added)

end data.«project-euler-statements».data.py.project_euler_statements.p88.naive
