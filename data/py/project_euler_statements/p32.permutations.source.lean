import data.«project-euler-statements».data.py.project_euler_statements.«p32.loops.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p32.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions ProjectEulerSolutions.PandigitalProductSearch
private abbrev program := P32Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)

def sources (items : List Nat) : List SequenceSource := (numbers items).map sequenceSource

def permutationBody : List Stmt :=
  [.assign [.name "digits"] (.builtinCall .list [.name "permutation"]),
   .forIn (.name "first") (.call (.name "range")
     [.constant (.int 1), .binOp (.name "width") .sub (.constant (.int 1))]) firstBody []]

theorem permutation_source :
    (executableBody ((findFunctionIn program.body "naive").getD ([], [])).2)[4]? =
      some (.forIn (.name "permutation") (.permutationsIterable [.name "pool", .constant .none])
        permutationBody []) := by rfl

theorem permutation_loop (width : Nat) (large : 3 ≤ width) (remaining : List (List Nat))
    (lengths : ∀ row ∈ remaining, row.length = width)
    (base : Mutable.Heap) (before : List Constant) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (getWidth : env "width" = some (number width))
    (getProducts : env "products" = some (.ref base.length)) :
    ∃ finalEnv extra, BlockContinues program env
      [.permutationStepLoop "permutation" (remaining.map sources) permutationBody []]
      (working base before garbage) finalEnv
      (working base (inserted before (remaining.flatMap (splitProducts width))) (garbage ++ extra)) ∧
      finalEnv "width" = some (number width) ∧
      finalEnv "products" = some (.ref base.length) := by
  induction remaining generalizing before garbage env with
  | nil =>
      refine ⟨env, [], ?_, getWidth, getProducts⟩
      simpa only [List.map_nil, List.flatMap_nil, inserted, List.map_nil, List.foldl_nil,
        List.append_nil] using (BlockContinues.permutation_done (module := program) (env := env)
          (heap := working base before garbage) BlockContinues.nil)
  | cons row remaining ih =>
      let current := working base before garbage
      obtain ⟨tuple, tupleExtra, allocated, tupleFound⟩ := HeapCollection.allocate_tuple (numbers row) current
      let tupleHeap := current ++ tupleExtra
      let bound := setLocal env "permutation" (.ref tuple)
      let ready := setLocal bound "digits" (.ref tupleHeap.length)
      let copiedGarbage := (garbage ++ tupleExtra) ++ [.list (numbers row)]
      have copied : BlockContinues program bound [permutationBody[0]'(by decide)] tupleHeap ready
          (working base before copiedGarbage) := by
        apply BlockContinues.assign
        simpa only [tupleHeap, copiedGarbage, current, working, List.append_assoc,
          List.singleton_append] using
          Evaluates.builtin (module := program) (env := bound)
            (.cons (Evaluates.lookup (name := "permutation") rfl) .nil)
            (primitive_list_tuple tupleHeap tuple (numbers row) tupleFound)
      have found : (working base before copiedGarbage)[tupleHeap.length]? =
          some (.list (numbers row)) := by
        simp [copiedGarbage, tupleHeap, current, working, List.append_assoc]
      obtain ⟨middle, splitExtra, scanned, stable⟩ := full_splits width tupleHeap.length row large
        (lengths row (by simp)) base before copiedGarbage ready found
        (by simp [ready, setLocal])
        (by simpa [ready, bound, setLocal] using getWidth)
        (by simpa [ready, bound, setLocal] using getProducts)
      have middleWidth := (stable "width" (by decide)).trans
        (by simpa [ready, bound, setLocal] using getWidth)
      have middleProducts := (stable "products" (by decide)).trans
        (by simpa [ready, bound, setLocal] using getProducts)
      obtain ⟨finalEnv, restExtra, completed, finalWidth, finalProducts⟩ := ih
        (fun item member => lengths item (by simp [member]))
        (inserted before (splitProducts width row)) (copiedGarbage ++ splitExtra) middle
        middleWidth middleProducts
      refine ⟨finalEnv, tupleExtra ++ [.list (numbers row)] ++ splitExtra ++ restExtra,
        ?_, finalWidth, finalProducts⟩
      apply BlockContinues.permutation_step (tuple := .ref tuple) (middle := tupleHeap)
        (by simpa [sources, numbers, List.map_map, Function.comp_def] using allocated)
      simpa [permutationBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        List.flatMap_cons, inserted_append, copiedGarbage, List.append_assoc] using
        copied.append (scanned.append completed)

theorem permutation_result (width address : Nat) (large : 3 ≤ width)
    (base : Mutable.Heap) (before : List Constant) (garbage : Mutable.Heap) (env : HeapCalls.Env)
    (found : (working base before garbage)[address]? = some (.list (numbers (List.range' 1 width))))
    (getPool : env "pool" = some (.ref address)) (getWidth : env "width" = some (number width))
    (getProducts : env "products" = some (.ref base.length)) :
    ∃ finalEnv extra, BlockContinues program env
      [.forIn (.name "permutation") (.permutationsIterable [.name "pool", .constant .none])
        permutationBody []]
      (working base before garbage) finalEnv
      (working base (inserted before (permutationProducts width)) (garbage ++ extra)) ∧
      finalEnv "products" = some (.ref base.length) := by
  obtain ⟨finalEnv, extra, scanned, _, finalProducts⟩ := permutation_loop width large
    (Permutations.rows width (List.range' 1 width)) (fun _ member => Permutations.row_length member)
    base before garbage env getWidth getProducts
  have rowsEq : (Permutations.rows width (List.range' 1 width)).map sources =
      (Permutations.rows width (List.range' 1 width)).map
        (fun row => (row.map number).map sequenceSource) := by
    apply List.map_congr_left
    intro row _
    rfl
  rw [rowsEq] at scanned
  refine ⟨finalEnv, extra, ?_, finalProducts⟩
  apply BlockContinues.for_permutations (.cons (Evaluates.lookup getPool) (.cons Evaluates.constant .nil))
  · simpa only [numbers, List.length_map, List.length_range', Permutations.rows_map,
      List.map_map, Function.comp_def, sources] using
      permutationRows_list (working base before garbage) address (numbers (List.range' 1 width)) found
  · simpa only [permutationProducts, List.map_map, Function.comp_def, comprehensionTargetName,
      comprehensionTargetBody] using scanned

end data.«project-euler-statements».data.py.project_euler_statements.p32.naive
