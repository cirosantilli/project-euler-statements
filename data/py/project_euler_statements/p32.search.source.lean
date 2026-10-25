import data.«project-euler-statements».data.py.project_euler_statements.«p32.permutations.source»

set_option Elab.async false

namespace data.«project-euler-statements».data.py.project_euler_statements.p32.naive
open FormalSW.PyAst HeapCalls ProjectEulerSolutions ProjectEulerSolutions.PandigitalProductSearch
private abbrev program := P32Ast.module
private abbrev number (n : Nat) : Mutable.Value := .scalar (.int n)
private abbrev flag (b : Bool) : Mutable.Value := .scalar (.bool b)
private abbrev code : List Stmt :=
  executableBody ((findFunctionIn program.body "naive").getD ([], [])).2

def readyEnv (env : HeapCalls.Env) (address : Nat) : HeapCalls.Env :=
  setLocal (setLocal env "products" (.ref address)) "pool" (.ref (address + 1))

theorem setup_result (width : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getWidth : env "width" = some (number width)) :
    ∃ extra, BlockContinues program env (code.drop 2 |>.take 2) heap
      (readyEnv env heap.length) (working heap [] (.list (numbers (List.range' 1 width)) :: extra)) := by
  let setHeap := heap ++ [.set []]
  let bound := setLocal env "products" (.ref heap.length)
  have allocated : BlockContinues program env [code[2]'(by decide)] heap bound setHeap :=
    BlockContinues.assign (Evaluates.builtin .nil rfl)
  have widthFound : bound "width" = some (number width) := by simpa [bound, setLocal] using getWidth
  obtain ⟨extra, pooled⟩ := HeapCollection.range_map (globals := []) program "$formalsw.range.item"
    (.name "$formalsw.range.item") number
    (fun heap env n found => ⟨[], by simpa using
      (Evaluates.lookup (module := program) (heap := heap) found)⟩)
    setHeap bound [.constant (.int 1), .binOp (.name "width") .add (.constant (.int 1))]
    [number 1, number (width + 1)] 1 width
    (.cons Evaluates.constant (.cons (Evaluates.binary (av := number width) (bv := number 1)
      (middle := setHeap) (afterRight := setHeap) (finalHeap := setHeap)
      (Evaluates.lookup widthFound) Evaluates.constant (by simp [Mutable.binary, scalarBinary])) .nil))
    (by change Except.ok (ε := ExceptionObject) ((1 : Int), ((width + 1 : Nat) : Int), (1 : Int)) =
          .ok (1, (1 : Int) + width, 1)
        simp only [Int.natCast_add, Int.natCast_one, Int.add_comm])
  refine ⟨extra, ?_⟩
  have copied := BlockContinues.assign (name := "pool") pooled
  simpa only [code, readyEnv, bound, setHeap, working, HeapCollection.working, numbers,
    List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] using
    allocated.append copied

theorem result (width : Nat) (large : 3 ≤ width) (small : width ≤ 9) (heap : Mutable.Heap) :
    ∃ finalHeap, SetCalls.ReturnsValue program "naive" [number width] heap
      (number (answer width)) finalHeap := by
  let entry := functionEnv ((findFunctionIn program.body "naive").getD ([], [])).1
    ((findFunctionIn program.body "naive").getD ([], [])).2 [number width] []
  let ready := readyEnv entry heap.length
  obtain ⟨garbage, setup⟩ := setup_result width heap entry rfl
  let poolObject : Mutable.Object := .list (numbers (List.range' 1 width))
  obtain ⟨finalEnv, extra, scanned, getProducts⟩ := permutation_result width (heap.length + 1) large heap []
    (poolObject :: garbage) ready (by simp [working, poolObject])
    (by simp [ready, readyEnv, setLocal]) (by simp [ready, readyEnv, setLocal, entry]; rfl)
    (by simp [ready, readyEnv, setLocal])
  have guarded : BlockContinues program entry (code.take 2) heap entry heap := by
    have low : BlockContinues program entry [code[0]'(by decide)] heap entry heap := by
      apply BlockContinues.branch (middle := heap) (flag := false) (value := flag false)
        (Evaluates.compare (av := number width) (bv := number 3) (middle := heap) (afterRight := heap)
          (Evaluates.lookup rfl) Evaluates.constant
          (by simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega)) rfl
      exact .nil
    have high : BlockContinues program entry [code[1]'(by decide)] heap entry heap := by
      apply BlockContinues.branch (middle := heap) (flag := false) (value := flag false)
        (Evaluates.compare (av := number width) (bv := number 9) (middle := heap) (afterRight := heap)
          (Evaluates.lookup rfl) Evaluates.constant
          (by simp [HeapCalls.compare, scalarCompare, evalCmpOp]; omega)) rfl
      exact .nil
    exact low.append high
  have exactSet : inserted [] (permutationProducts width) =
      ((permutationProducts width).eraseDups.map fun (n : Nat) => Constant.int n) := by
    simpa only [inserted] using ScalarSet.fold_insert_nats (permutationProducts width)
  have sumCast (items : List Nat) : (items.map (fun (n : Nat) => (n : Int))).sum = (items.sum : Int) := by
    induction items with
    | nil => rfl
    | cons n rest ih => simp [ih]
  let finalHeap := working heap (inserted [] (permutationProducts width)) ((poolObject :: garbage) ++ extra)
  have found : finalHeap[heap.length]? =
      some (.set ((((permutationProducts width).eraseDups).map (fun (n : Nat) => (n : Int))).map Constant.int)) := by
    simpa only [finalHeap, exactSet, List.map_map, Function.comp_def] using
      working_found heap (inserted [] (permutationProducts width)) ((poolObject :: garbage) ++ extra)
  have summed := SetCalls.Evaluates.sum_integers
    (items := (permutationProducts width).eraseDups.map (fun (n : Nat) => (n : Int)))
    (initial := 0) (module := program) (env := finalEnv) (globals := [])
    (iterable := .name "products") (start := .constant (.int 0))
    (.cons (Evaluates.lookup getProducts) (.cons Evaluates.constant .nil)) found
  refine ⟨finalHeap, ?_⟩
  apply SetCalls.BlockReturns.function rfl rfl
  apply SetCalls.BlockReturns.after_heap guarded
  apply SetCalls.BlockReturns.after_heap setup
  apply SetCalls.BlockReturns.after_heap scanned
  apply SetCalls.BlockReturns.return_value
  simpa only [Int.zero_add, sumCast, permutation_answer width small] using summed


theorem result_int (width : Int) (heap : Mutable.Heap) :
    ∃ finalHeap, SetCalls.ReturnsValue program "naive" [.scalar (.int width)] heap
      (number (answer width.toNat)) finalHeap := by
  by_cases low : width < 3
  · refine ⟨heap, SetCalls.ReturnsValue.of_heap ?_⟩
    rw [answer_small width.toNat (by omega)]
    apply HeapCalls.BlockReturns.function rfl rfl
    apply HeapCalls.BlockReturns.branch (flag := true) (value := flag true) (middle := heap)
    · exact Evaluates.compare (av := .scalar (.int width)) (bv := number 3)
        (middle := heap) (afterRight := heap) (Evaluates.lookup rfl) Evaluates.constant
        (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, low])
    · rfl
    · exact HeapCalls.BlockReturns.return_value Evaluates.constant
  · by_cases high : 9 < width
    · refine ⟨heap, SetCalls.ReturnsValue.of_heap ?_⟩
      rw [answer_large width.toNat (by omega)]
      apply HeapCalls.BlockReturns.function rfl rfl
      apply HeapCalls.BlockReturns.branch (flag := false) (value := flag false) (middle := heap)
      · exact Evaluates.compare (av := .scalar (.int width)) (bv := number 3)
          (middle := heap) (afterRight := heap) (Evaluates.lookup rfl) Evaluates.constant
          (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, low])
      · rfl
      · apply HeapCalls.BlockReturns.branch (flag := true) (value := flag true) (middle := heap)
        · exact Evaluates.compare (av := .scalar (.int width)) (bv := number 9)
            (middle := heap) (afterRight := heap) (Evaluates.lookup rfl) Evaluates.constant
            (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, high])
        · rfl
        · exact HeapCalls.BlockReturns.return_value Evaluates.constant
    · lift width to Nat using (by omega : 0 ≤ width)
      exact result width (by omega) (by omega) heap

end data.«project-euler-statements».data.py.project_euler_statements.p32.naive
