import data.«project-euler-statements».data.py.project_euler_statements.«p32.collect.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p32.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.PandigitalProductSearch
private abbrev program := P32Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)

def rowSlice (items : List Nat) (first second count : Nat) : List Nat :=
  (List.range' second count).flatMap (selected items first)

theorem inner_loop (items : List Nat) (first second count stop address : Nat)
    (ordered : first ≤ second) (endpoint : second + count = stop) (bound : stop ≤ items.length)
    (base : Mutable.Heap) (before : List Constant) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (found : (working base before garbage)[address]? = some (.list (numbers items)))
    (getDigits : env "digits" = some (.ref address)) (getFirst : env "first" = some (number first))
    (getProducts : env "products" = some (.ref base.length)) :
    ∃ finalEnv extra, BlockContinues program env
      [.rangeStepLoop "second" second stop 1 candidateBody []]
      (working base before garbage) finalEnv
      (working base (inserted before (rowSlice items first second count)) (garbage ++ extra)) ∧
      Stable env finalEnv := by
  have different : address ≠ base.length := by
    intro same
    rw [same, working_found] at found
    cases found
  induction count generalizing second before garbage env with
  | zero =>
      refine ⟨env, [], ?_, fun _ _ => rfl⟩
      simpa only [rowSlice, List.range'_zero, List.flatMap_nil, inserted, List.map_nil,
        List.foldl_nil, List.append_nil] using
        (BlockContinues.range_done (module := program) (env := env) (name := "second")
          (next := second) (stop := stop) (stride := 1) (body := candidateBody) (otherwise := [])
          (heap := working base before garbage) (by simp [Calls.rangeContinues]; omega) .nil)
  | succ count ih =>
      let ready := setLocal env "second" (number second)
      obtain ⟨middle, allocated, executed, middleFirst, middleStable⟩ :=
        candidate_result items first second address ordered (by omega) base before garbage ready found
          (by simpa [ready, setLocal] using getDigits) (by simpa [ready, setLocal] using getFirst)
          (by simp [ready, setLocal]) (by simpa [ready, setLocal] using getProducts)
      have kept := other_found base before (inserted before (selected items first second)) garbage allocated
        address (.list (numbers items)) different found
      obtain ⟨finalEnv, extra, completed, finalStable⟩ := ih (second + 1) (by omega) (by omega)
        (inserted before (selected items first second)) (garbage ++ allocated) middle kept
        ((middleStable "digits" (by decide)).trans (by simpa [ready, setLocal] using getDigits))
        middleFirst
        ((middleStable "products" (by decide)).trans (by simpa [ready, setLocal] using getProducts))
      refine ⟨finalEnv, allocated ++ extra, ?_, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa [rowSlice, List.range'_succ, inserted_append, List.append_assoc, candidateBody,
          Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using executed.append completed
      · intro query unchanged
        have outside : query ≠ "second" := fun equal => unchanged (by simp [writes, equal])
        exact (finalStable query unchanged).trans ((middleStable query unchanged).trans
          (by simp [ready, setLocal, outside]))

def firstBody : List Stmt :=
  [.forIn (.name "second") (.call (.name "range")
    [.binOp (.name "first") .add (.constant (.int 1)), .name "width"]) candidateBody []]

theorem row_result (width first address : Nat) (items : List Nat)
    (within : first + 1 ≤ width) (bound : width ≤ items.length)
    (base : Mutable.Heap) (before : List Constant) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (found : (working base before garbage)[address]? = some (.list (numbers items)))
    (getDigits : env "digits" = some (.ref address)) (getFirst : env "first" = some (number first))
    (getWidth : env "width" = some (number width))
    (getProducts : env "products" = some (.ref base.length)) :
    ∃ finalEnv extra, BlockContinues program env firstBody (working base before garbage) finalEnv
      (working base (inserted before (rowSlice items first (first + 1) (width - first - 1)))
        (garbage ++ extra)) ∧ Stable env finalEnv := by
  obtain ⟨finalEnv, extra, scanned, stable⟩ := inner_loop items first (first + 1) (width - first - 1)
    width address (by omega) (by omega) bound base before garbage env found getDigits getFirst getProducts
  refine ⟨finalEnv, extra, ?_, stable⟩
  apply BlockContinues.for_range (values := [number (first + 1), number width])
    (.cons (Evaluates.binary (av := number first) (bv := number 1)
      (middle := working base before garbage) (afterRight := working base before garbage)
      (Evaluates.lookup getFirst) Evaluates.constant (by simp [Mutable.binary, scalarBinary]))
      (.cons (Evaluates.lookup getWidth) .nil)) rfl scanned

theorem first_loop (width first count address : Nat) (items : List Nat)
    (positive : 0 < first) (endpoint : first + count = width - 1) (bound : width ≤ items.length)
    (base : Mutable.Heap) (before : List Constant) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (found : (working base before garbage)[address]? = some (.list (numbers items)))
    (getDigits : env "digits" = some (.ref address)) (getWidth : env "width" = some (number width))
    (getProducts : env "products" = some (.ref base.length)) :
    ∃ finalEnv extra, BlockContinues program env
      [.rangeStepLoop "first" first ((width : Int) - 1) 1 firstBody []]
      (working base before garbage) finalEnv
      (working base (inserted before ((List.range' first count).flatMap fun index =>
        rowSlice items index (index + 1) (width - index - 1))) (garbage ++ extra)) ∧
      Stable env finalEnv := by
  have different : address ≠ base.length := by
    intro same
    rw [same, working_found] at found
    cases found
  induction count generalizing first before garbage env with
  | zero =>
      refine ⟨env, [], ?_, fun _ _ => rfl⟩
      simpa only [List.range'_zero, List.flatMap_nil, inserted, List.map_nil,
        List.foldl_nil, List.append_nil] using
        (BlockContinues.range_done (module := program) (env := env) (name := "first")
          (next := first) (stop := (width : Int) - 1) (stride := 1) (body := firstBody) (otherwise := [])
          (heap := working base before garbage) (by simp [Calls.rangeContinues]; omega) .nil)
  | succ count ih =>
      let ready := setLocal env "first" (number first)
      obtain ⟨middle, allocated, executed, middleStable⟩ := row_result width first address items
        (by omega) bound base before garbage ready found
        (by simpa [ready, setLocal] using getDigits) (by simp [ready, setLocal])
        (by simpa [ready, setLocal] using getWidth) (by simpa [ready, setLocal] using getProducts)
      have kept := other_found base before
        (inserted before (rowSlice items first (first + 1) (width - first - 1))) garbage allocated
        address (.list (numbers items)) different found
      obtain ⟨finalEnv, extra, completed, finalStable⟩ := ih (first + 1) (by omega) (by omega)
        (inserted before (rowSlice items first (first + 1) (width - first - 1)))
        (garbage ++ allocated) middle kept
        ((middleStable "digits" (by decide)).trans (by simpa [ready, setLocal] using getDigits))
        ((middleStable "width" (by decide)).trans (by simpa [ready, setLocal] using getWidth))
        ((middleStable "products" (by decide)).trans (by simpa [ready, setLocal] using getProducts))
      refine ⟨finalEnv, allocated ++ extra, ?_, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues]; omega)
        simpa [List.range'_succ, inserted_append, List.append_assoc, firstBody, candidateBody,
          Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt] using executed.append completed
      · intro query unchanged
        have outside : query ≠ "first" := fun equal => unchanged (by simp [writes, equal])
        exact (finalStable query unchanged).trans ((middleStable query unchanged).trans
          (by simp [ready, setLocal, outside]))

theorem full_splits (width address : Nat) (items : List Nat) (large : 3 ≤ width) (length : items.length = width)
    (base : Mutable.Heap) (before : List Constant) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (found : (working base before garbage)[address]? = some (.list (numbers items)))
    (getDigits : env "digits" = some (.ref address)) (getWidth : env "width" = some (number width))
    (getProducts : env "products" = some (.ref base.length)) :
    ∃ finalEnv extra, BlockContinues program env
      [.forIn (.name "first") (.call (.name "range")
        [.constant (.int 1), .binOp (.name "width") .sub (.constant (.int 1))]) firstBody []]
      (working base before garbage) finalEnv
      (working base (inserted before (splitProducts width items)) (garbage ++ extra)) ∧ Stable env finalEnv := by
  obtain ⟨finalEnv, extra, scanned, stable⟩ := first_loop width 1 (width - 2) address items
    (by decide) (by omega) (by omega) base before garbage env found getDigits getWidth getProducts
  refine ⟨finalEnv, extra, ?_, stable⟩
  apply BlockContinues.for_range (values := [number 1, .scalar (.int ((width : Int) - 1))])
    (.cons Evaluates.constant (.cons (Evaluates.binary (av := number width) (bv := number 1)
      (middle := working base before garbage) (afterRight := working base before garbage)
      (finalHeap := working base before garbage)
      (Evaluates.lookup getWidth) Evaluates.constant (by simp [Mutable.binary, scalarBinary])) .nil)) rfl
  simpa only [splitProducts, rowSlice, selected, partDigits] using scanned

end data.«project-euler-statements».data.py.project_euler_statements.p32.naive
