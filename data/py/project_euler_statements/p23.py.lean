import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p23.py.ast»
import data.«project-euler-statements».data.py.project_euler_statements.«common.py»
import FormalSW
import ProjectEulerStatements.P23
import Mathlib.Data.List.Range
import Mathlib.Data.List.Perm.Basic

namespace data.«project-euler-statements».data.py.project_euler_statements.p23
open FormalSW.PyAst HeapCalls
private abbrev program := P23Ast.module
private abbrev number (n : Int) : Mutable.Value := .scalar (.int n)

private def selectedSum (test : Nat → Bool) (start count : Nat) : Nat :=
  ((List.range' start count).filter test).sum

private abbrev divisorTest : Expr :=
  .compare (.binOp (.name "n") .mod (.name "d")) [(.eq, .constant (.int 0))]
private abbrev divisorBody : List Stmt :=
  comprehensionFilters [divisorTest] (sumBody (.name "d") [])

private theorem divisor_loop (n count start : Nat) (positive : 0 < start)
    (total : Nat) (heap : Mutable.Heap) (env : HeapCalls.Env)
    (getN : env "n" = some (number n))
    (getTotal : env sumAccumulator = some (number total)) :
    BlockReturns program env
      [.rangeStepLoop "d" start (start + count) 1 divisorBody [], .return (.name sumAccumulator)]
      heap (number (total + selectedSum (fun d => decide (n % d = 0)) start count)) heap := by
  induction count generalizing start total env with
  | zero =>
      apply BlockReturns.range_done (by simp [Calls.rangeContinues])
      simpa [selectedSum] using BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let boundEnv := setLocal env "d" (number start)
      have tested : Evaluates program boundEnv divisorTest heap
          (.scalar (.bool (decide (n % start = 0)))) heap := by
        apply Evaluates.compare (av := number (n % start)) (bv := number 0) (middle := heap) (afterRight := heap)
        · apply Evaluates.binary (av := number n) (bv := number start) (middle := heap) (afterRight := heap)
            (Evaluates.lookup (by simpa [boundEnv, setLocal] using getN))
            (Evaluates.lookup (by simp [boundEnv, setLocal]))
          simp [Mutable.binary, scalarBinary, number, positive, positive.ne']
        · exact Evaluates.constant
        · simp [HeapCalls.compare, scalarCompare, evalCmpOp, ← Int.dvd_iff_emod_eq_zero,
            Int.natCast_dvd_natCast, Nat.dvd_iff_mod_eq_zero]
      apply BlockReturns.range_step (by simp [Calls.rangeContinues])
      by_cases divides : n % start = 0
      · apply BlockReturns.branch (flag := true) (by simpa [divides] using tested) rfl
        apply BlockReturns.assign (value := number (total + start)) (middle := heap)
        · apply Evaluates.binary (av := number total) (bv := number start)
            (Evaluates.lookup (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal))
            (Evaluates.lookup rfl)
          simp [Mutable.binary, scalarBinary, number]
        · simpa [divisorBody, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            selectedSum, List.range'_succ, divides, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Int.add_assoc, Int.add_left_comm, Int.add_comm]
            using ih (start + 1) (by omega) (total + start)
              (setLocal boundEnv sumAccumulator (number (total + start)))
              (by simpa [boundEnv, setLocal, sumAccumulator] using getN) (by simp [setLocal])
      · apply BlockReturns.branch (flag := false) (by simpa [divides] using tested) rfl
        simpa [divisorBody, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
            selectedSum, List.range'_succ, divides, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Int.add_assoc, Int.add_left_comm, Int.add_comm]
          using ih (start + 1) (by omega) total boundEnv
            (by simpa [boundEnv, setLocal] using getN)
            (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal)

private theorem selectedSum_interval (test : Nat → Bool) (n : Nat) :
    selectedSum test 1 (n - 1) =
      ((Finset.Icc 1 (n - 1)).filter (fun d => test d = true)).sum (fun d => d) := by
  have same : ((List.range' 1 (n - 1)).filter test).toFinset =
      (Finset.Icc 1 (n - 1)).filter (fun d => test d = true) := by
    ext d
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range', Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨k, lower, rfl⟩, accepted⟩
      exact ⟨⟨by omega, by omega⟩, accepted⟩
    · rintro ⟨⟨lower, upper⟩, accepted⟩
      exact ⟨⟨d - 1, by omega, by omega⟩, accepted⟩
  rw [← same, List.sum_toFinset]
  · simp [selectedSum]
  · exact (List.nodup_range' (s := 1) (n := n - 1)).filter _

theorem proper_divisor_sum.result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "proper_divisor_sum" [number n] heap
      (number (ProjectEulerStatements.P23.divisorSum n)) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  by_cases zero : n = 0
  · subst n
    apply Evaluates.conditional (Evaluates.lookup rfl) (flag := false) rfl
    simpa [ProjectEulerStatements.P23.divisorSum, ProjectEulerStatements.P23.properDivisors]
      using (Evaluates.constant (module := program) (heap := heap) (value := .int 0) (env := _))
  · apply Evaluates.conditional (Evaluates.lookup rfl) (flag := true)
      (by simp [Mutable.truth, scalarTruth, zero])
    apply Evaluates.sum_range
    apply Evaluates.sum_generator_range
      (.cons Evaluates.constant (.cons (Evaluates.lookup rfl) .nil)) rfl Evaluates.constant rfl
    have result := divisor_loop n (n - 1) 1 (by decide) 0 heap
      (setLocal (comprehensionEnv (functionEnv [⟨"n", some (.name "int"), none⟩] [] [number n] [])
        [("d", .call (.name "range") [.constant (.int 1), .name "n"], [divisorTest])])
        sumAccumulator (number 0)) rfl rfl
    have count : (1 : Int) + (n - 1 : Nat) = n := by omega
    simpa [count, selectedSum_interval, ProjectEulerStatements.P23.divisorSum,
      ProjectEulerStatements.P23.properDivisors, Nat.dvd_iff_mod_eq_zero] using result

theorem divisor_sum.result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "divisor_sum" [number n] heap
      (number (ProjectEulerStatements.P23.divisorSum n)) heap := by
  apply BlockReturns.function rfl rfl
  exact BlockReturns.return_value
    (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (proper_divisor_sum.result n heap))

theorem is_abundant.result (n : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "is_abundant" [number n] heap
      (.scalar (.bool (decide (ProjectEulerStatements.P23.isAbundant n)))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.compare (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (divisor_sum.result n heap))
    (Evaluates.lookup rfl)
  simp [HeapCalls.compare, scalarCompare, evalCmpOp, ProjectEulerStatements.P23.isAbundant]

private abbrev encode (items : List Nat) : List Constant :=
  items.map (fun (n : Nat) => .int (n : Int))

private theorem contains_nats (items : List Nat) (value : Nat) :
    ScalarSet.contains (encode items) (.int value) = decide (value ∈ items) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      change ((scalarCompare .eq (.int head) (.int value)).getD false ||
        ScalarSet.contains (encode tail) (.int value)) = _
      rw [ih]
      simp [scalarCompare, evalCmpOp, eq_comm]

private abbrev abundantTest : Expr := .call (.name "is_abundant") [.name "n"]
private abbrev abundantBody (address : Nat) : List Stmt :=
  [.ifThen abundantTest [.comprehensionAdd address (.name "n")] []]

private theorem abundant_loop (count start : Nat) (collected : List Nat)
    (earlier : ∀ n ∈ collected, n < start) (heap : Mutable.Heap) (env : HeapCalls.Env) :
    ∃ finalEnv, BlockContinues program env
      [.rangeStepLoop "n" start (start + count) 1 (abundantBody heap.length) []]
      (heap ++ [.set (encode collected)]) finalEnv
      (heap ++ [.set (encode (collected ++
        (List.range' start count).filter (fun n => decide (ProjectEulerStatements.P23.isAbundant n))))]) := by
  induction count generalizing start collected env with
  | zero =>
      refine ⟨env, ?_⟩
      simpa using BlockContinues.range_done (module := program) (body := abundantBody heap.length)
        (by simp [Calls.rangeContinues]) BlockContinues.nil
  | succ count ih =>
      let boundEnv := setLocal env "n" (number start)
      have tested : Evaluates program boundEnv abundantTest (heap ++ [.set (encode collected)])
          (.scalar (.bool (decide (ProjectEulerStatements.P23.isAbundant start))))
          (heap ++ [.set (encode collected)]) :=
        Evaluates.call (.cons (Evaluates.lookup rfl) .nil)
          (is_abundant.result start (heap ++ [.set (encode collected)]))
      let nextItems := if ProjectEulerStatements.P23.isAbundant start then collected ++ [start] else collected
      have nextEarlier : ∀ n ∈ nextItems, n < start + 1 := by
        intro n member
        dsimp [nextItems] at member
        split at member
        · simp only [List.mem_append, List.mem_singleton] at member
          rcases member with member | rfl
          · have := earlier n member
            omega
          · omega
        · have := earlier n member
          omega
      have executed : BlockContinues program boundEnv (abundantBody heap.length)
          (heap ++ [.set (encode collected)]) boundEnv (heap ++ [.set (encode nextItems)]) := by
        by_cases abundant : ProjectEulerStatements.P23.isAbundant start
        · apply BlockContinues.branch (flag := true) (by simpa [abundant] using tested) rfl
          have missing : start ∉ collected := by
            intro member
            have := earlier start member
            omega
          have emitted := BlockContinues.comprehension_add (globals := []) (module := program)
            (env := boundEnv) (address := heap.length) (heap := heap ++ [.set (encode collected)])
            (Evaluates.lookup (name := "n") rfl)
            (by simp : (heap ++ [.set (encode collected)])[heap.length]? = some (.set (encode collected)))
          have inserted : ScalarSet.insert (encode collected) (.int start) = encode (collected ++ [start]) := by
            rw [ScalarSet.insert, contains_nats]
            simp [missing, encode]
          simpa [inserted, nextItems, abundant] using emitted
        · simpa [abundantBody, nextItems, abundant] using
            BlockContinues.branch (yes := [.comprehensionAdd heap.length (.name "n")]) (no := [])
              (flag := false) (by simpa [abundant] using tested) rfl BlockContinues.nil
      obtain ⟨finalEnv, rest⟩ := ih (start + 1) nextItems nextEarlier boundEnv
      refine ⟨finalEnv, ?_⟩
      apply BlockContinues.range_step (by simp [Calls.rangeContinues])
      by_cases abundant : ProjectEulerStatements.P23.isAbundant start
      all_goals simpa [abundantBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
        nextItems, abundant, List.range'_succ, List.append_assoc, Int.add_assoc, Int.add_comm,
        Int.add_left_comm] using executed.append rest

/-- The stored representatives are increasing; set traversal may still choose any order. -/
def abundantItems (limit : Nat) : List Nat :=
  (List.range' 1 limit).filter (fun n => decide (ProjectEulerStatements.P23.isAbundant n))

theorem abundant_set.result (limit : Nat) (heap : Mutable.Heap) :
    ReturnsValue program "abundant_set" [number limit] heap (.ref heap.length)
      (heap ++ [.set (encode (abundantItems limit))]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  obtain ⟨finalEnv, executed⟩ := abundant_loop limit 1 [] (by simp) heap
    (comprehensionTargetsEnv
      (functionEnv [⟨"limit", some (.name "int"), none⟩] [] [number limit] [])
      [(.name "n", .call (.name "range") [.constant (.int 1), .binOp (.name "limit") .add (.constant (.int 1))],
        [abundantTest])])
  apply Evaluates.set_comp_range (finalEnv := finalEnv)
    (.cons Evaluates.constant (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil)) rfl
  simpa [abundantItems, abundantBody, abundantTest, comprehensionTargetName, comprehensionTargetBody,
    comprehensionTargetsBody, comprehensionFilters, Int.add_comm] using executed

theorem abundant_set.negative (limit : Int) (negative : limit < 0) (heap : Mutable.Heap) :
    ReturnsValue program "abundant_set" [number limit] heap (.ref heap.length) (heap ++ [.set []]) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.set_comp_range
    (.cons Evaluates.constant (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil)) rfl
  exact BlockContinues.range_done (by simp [Calls.rangeContinues]; omega) BlockContinues.nil

theorem abundantItems_mem (limit n : Nat) :
    n ∈ abundantItems limit ↔ n ∈ ProjectEulerStatements.P23.abundantSet limit := by
  simp only [abundantItems, List.mem_filter, List.mem_range',
    ProjectEulerStatements.P23.abundantSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨k, bound, rfl⟩, abundant⟩
    exact ⟨⟨by omega, by omega⟩, of_decide_eq_true abundant⟩
  · rintro ⟨⟨lower, upper⟩, abundant⟩
    exact ⟨⟨n - 1, by omega, by omega⟩, decide_eq_true abundant⟩

private def insertNat (items : List Nat) (value : Nat) : List Nat :=
  if value ∈ items then items else items ++ [value]

private theorem insertNat_mem (items : List Nat) (value n : Nat) :
    n ∈ insertNat items value ↔ n ∈ items ∨ n = value := by
  by_cases present : value ∈ items
  · simp [insertNat, present]
    intro equal
    simpa [equal] using present
  · simp [insertNat, present]

private theorem insertNat_encode (items : List Nat) (value : Nat) :
    ScalarSet.insert (encode items) (.int value) = encode (insertNat items value) := by
  rw [ScalarSet.insert, contains_nats]
  by_cases present : value ∈ items <;> simp [present, insertNat, encode]

private abbrev pairHeap (abundants collected : List Nat) : Mutable.Heap :=
  [.set (encode abundants), .set (encode collected)]
private abbrev pairBody : List Stmt :=
  [.expr (.call (.attribute (.name "can") "add") [.binOp (.name "a") .add (.name "b")])]

/-- Every schedule adds exactly the sums with the unvisited second operands. -/
private theorem inner_loop (choices : ChoiceSchedule) (abundants remaining collected : List Nat)
    (a : Nat) (env : HeapCalls.Env) (getA : env "a" = some (number a))
    (getCan : env "can" = some (.ref 1))
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) (used : Nat) :
    ∃ finalEnv finalItems finalUsed,
      (∀ n, n ∈ finalItems ↔ n ∈ collected ∨ ∃ b ∈ remaining, a + b = n) ∧
      (∀ key, key ≠ "b" → finalEnv key = env key) ∧
      SetCalls.Reaches choices program anchors
        ⟨⟨.block (.setStepLoop "b" 0 (encode abundants) (encode remaining) pairBody [] :: following) env,
          stack, pairHeap abundants collected⟩, used⟩
        ⟨⟨.block following finalEnv, stack, pairHeap abundants finalItems⟩, finalUsed⟩ := by
  cases remaining with
  | nil =>
      refine ⟨env, collected, used, ?_, ?_, .next ?_ .refl⟩
      · simp
      · simp
      · simp [SetCalls.step, HeapCalls.step, SetCalls.iteratorStep, pairHeap, show encode [] = [] from rfl]
  | cons head tail =>
      let index := choices used % (head :: tail).length
      have bound : index < (head :: tail).length := Nat.mod_lt _ (by simp)
      let item := (head :: tail)[index]
      have selected : (head :: tail)[index]? = some item := List.getElem?_eq_getElem bound
      have selected' : (head :: tail)[choices used % (tail.length + 1)]? = some item := selected
      let rest := (head :: tail).eraseIdx index
      let boundEnv := setLocal env "b" (number item)
      let updated := insertNat collected (a + item)
      have emitted : BlockContinues program boundEnv pairBody (pairHeap abundants collected)
          boundEnv (pairHeap abundants updated) := by
        apply BlockContinues.discard
        have added := Evaluates.add (globals := []) (module := program) (env := boundEnv)
          (heap := pairHeap abundants collected) (middle := pairHeap abundants collected)
          (afterItem := pairHeap abundants collected) (address := 1)
          (Evaluates.lookup (name := "can") (by simpa [boundEnv, setLocal] using getCan)) rfl
          (Evaluates.binary (av := number a) (bv := number item)
            (Evaluates.lookup (name := "a") (by simpa [boundEnv, setLocal] using getA)) (Evaluates.lookup (name := "b") rfl)
            (show Mutable.binary .add (number a) (number item) (pairHeap abundants collected) =
              some (.ok (number ↑(a + item)), pairHeap abundants collected) by
                simp [Mutable.binary, scalarBinary, number])) rfl
        rw [insertNat_encode] at added
        simpa [pairHeap, updated] using added
      obtain ⟨finalEnv, finalItems, finalUsed, members, preserved, completed⟩ :=
        inner_loop choices abundants rest updated a boundEnv
          (by simpa [boundEnv, setLocal] using getA)
          (by simpa [boundEnv, setLocal] using getCan) following anchors stack (used + 1)
      refine ⟨finalEnv, finalItems, finalUsed, ?_, ?_, ?_⟩
      · intro n
        rw [members, insertNat_mem]
        have same : ∀ b, b ∈ head :: tail ↔ b = item ∨ b ∈ rest := by
          intro b
          simpa [item, rest] using ((List.getElem_cons_eraseIdx_perm bound).mem_iff (a := b)).symm
        simp only [same]
        constructor
        · rintro ((member | equal) | ⟨b, member, equal⟩)
          · exact .inl member
          · exact .inr ⟨item, .inl rfl, equal.symm⟩
          · exact .inr ⟨b, .inr member, equal⟩
        · rintro (member | ⟨b, member | member, equal⟩)
          · exact .inl (.inl member)
          · subst b
            exact .inl (.inr equal.symm)
          · exact .inr ⟨b, member, equal⟩
      · intro key different
        rw [preserved key different]
        simp [boundEnv, setLocal, different]
      · apply SetCalls.Reaches.next (following :=
          ⟨⟨.block (pairBody ++ [.setStepLoop "b" 0 (encode abundants) (encode rest) pairBody []] ++ following)
            boundEnv, stack, pairHeap abundants collected⟩, used + 1⟩)
        · have chosen : (encode (head :: tail))[choices used % (tail.length + 1)]? = some (.int item) := by
            simp only [encode, List.getElem?_map, selected', Option.map_some]
          have erased : (encode (head :: tail)).eraseIdx index = encode rest :=
            List.eraseIdx_map _ _ _
          simp only [SetCalls.step, HeapCalls.step, SetCalls.iteratorStep, pairHeap,
            List.getElem?_cons_zero,
            show encode (head :: tail) = .int head :: encode tail from rfl,
            List.length_cons, show (encode tail).length = tail.length from List.length_map ..] at chosen erased ⊢
          simp [chosen, ← erased, index, pairBody, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt, boundEnv, number]
        · exact (SetCalls.Reaches.of_heap (emitted
            (.setStepLoop "b" 0 (encode abundants) (encode rest) pairBody [] :: following) anchors stack)
            choices (used + 1)).trans completed
termination_by remaining.length
decreasing_by
  change ((head :: tail).eraseIdx index).length < (head :: tail).length
  rw [List.length_eraseIdx_of_lt bound]
  simp

private theorem enter_set (choices : ChoiceSchedule) (env : HeapCalls.Env) (heap : Mutable.Heap)
    (source name : String) (address : Nat) (items : List Constant)
    (lookup : env source = some (.ref address)) (found : heap[address]? = some (.set items))
    (body otherwise following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) (used : Nat) :
    SetCalls.Reaches choices program anchors
      ⟨⟨.block (.forIn (.name name) (.name source) body otherwise :: following) env, stack, heap⟩, used⟩
      ⟨⟨.block (.setStepLoop name address items items body otherwise :: following) env, stack, heap⟩, used⟩ := by
  apply SetCalls.Reaches.next rfl
  apply (SetCalls.Reaches.of_heap (Evaluates.lookup (module := program) (heap := heap) lookup
    anchors (.sequence name body otherwise following env :: stack)) choices used).trans
  exact .next (by simp [SetCalls.step, HeapCalls.step, HeapCalls.run, Mutable.sequence, found,
    SetCalls.iteratorStep, Mutable.unsupported]) .refl

private abbrev outerBody : List Stmt := [.forIn (.name "b") (.name "abundants") pairBody []]

/-- Independent traversal choices in both loops still cover every ordered pair. -/
private theorem outer_loop (choices : ChoiceSchedule) (abundants remaining collected : List Nat)
    (env : HeapCalls.Env) (getAbundants : env "abundants" = some (.ref 0))
    (getCan : env "can" = some (.ref 1))
    (following : List Stmt) (anchors : Nat) (stack : List HeapCalls.Frame) (used : Nat) :
    ∃ finalEnv finalItems finalUsed,
      (∀ n, n ∈ finalItems ↔ n ∈ collected ∨ ∃ a ∈ remaining, ∃ b ∈ abundants, a + b = n) ∧
      (∀ key, key ≠ "a" → key ≠ "b" → finalEnv key = env key) ∧
      SetCalls.Reaches choices program anchors
        ⟨⟨.block (.setStepLoop "a" 0 (encode abundants) (encode remaining) outerBody [] :: following) env,
          stack, pairHeap abundants collected⟩, used⟩
        ⟨⟨.block following finalEnv, stack, pairHeap abundants finalItems⟩, finalUsed⟩ := by
  cases remaining with
  | nil =>
      refine ⟨env, collected, used, ?_, ?_, .next ?_ .refl⟩
      · simp
      · simp
      · simp [SetCalls.step, HeapCalls.step, SetCalls.iteratorStep, pairHeap, show encode [] = [] from rfl]
  | cons head tail =>
      let index := choices used % (head :: tail).length
      have bound : index < (head :: tail).length := Nat.mod_lt _ (by simp)
      let item := (head :: tail)[index]
      have selected : (head :: tail)[index]? = some item := List.getElem?_eq_getElem bound
      have selected' : (head :: tail)[choices used % (tail.length + 1)]? = some item := selected
      let rest := (head :: tail).eraseIdx index
      let boundEnv := setLocal env "a" (number item)
      let continuation := .setStepLoop "a" 0 (encode abundants) (encode rest) outerBody [] :: following
      obtain ⟨middleEnv, middleItems, middleUsed, innerMembers, innerPreserved, inner⟩ :=
        inner_loop choices abundants abundants collected item boundEnv rfl
          (by simpa [boundEnv, setLocal] using getCan) continuation anchors stack (used + 1)
      have savedAbundants : middleEnv "abundants" = some (.ref 0) := by
        rw [innerPreserved "abundants" (by decide)]
        simpa [boundEnv, setLocal] using getAbundants
      have savedCan : middleEnv "can" = some (.ref 1) := by
        rw [innerPreserved "can" (by decide)]
        simpa [boundEnv, setLocal] using getCan
      obtain ⟨finalEnv, finalItems, finalUsed, members, preserved, completed⟩ :=
        outer_loop choices abundants rest middleItems middleEnv savedAbundants savedCan following anchors stack middleUsed
      refine ⟨finalEnv, finalItems, finalUsed, ?_, ?_, ?_⟩
      · intro n
        rw [members, innerMembers]
        have same : ∀ a, a ∈ head :: tail ↔ a = item ∨ a ∈ rest := by
          intro a
          simpa [item, rest] using ((List.getElem_cons_eraseIdx_perm bound).mem_iff (a := a)).symm
        simp only [same]
        constructor
        · rintro ((member | sums) | ⟨a, member, sums⟩)
          · exact .inl member
          · exact .inr ⟨item, .inl rfl, sums⟩
          · exact .inr ⟨a, .inr member, sums⟩
        · rintro (member | ⟨a, member | member, sums⟩)
          · exact .inl (.inl member)
          · subst a
            exact .inl (.inr sums)
          · exact .inr ⟨a, member, sums⟩
      · intro key notA notB
        rw [preserved key notA notB, innerPreserved key notB]
        simp [boundEnv, setLocal, notA]
      · apply SetCalls.Reaches.next (following :=
          ⟨⟨.block (outerBody ++ continuation) boundEnv, stack, pairHeap abundants collected⟩, used + 1⟩)
        · have chosen : (encode (head :: tail))[choices used % (tail.length + 1)]? = some (.int item) := by
            simp only [encode, List.getElem?_map, selected', Option.map_some]
          have erased : (encode (head :: tail)).eraseIdx index = encode rest := List.eraseIdx_map _ _ _
          simp only [SetCalls.step, HeapCalls.step, SetCalls.iteratorStep, pairHeap,
            List.getElem?_cons_zero,
            show encode (head :: tail) = .int head :: encode tail from rfl,
            List.length_cons, show (encode tail).length = tail.length from List.length_map ..] at chosen erased ⊢
          simp [chosen, ← erased, index, outerBody, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt, boundEnv, number, continuation]
        · have entry := enter_set choices boundEnv (pairHeap abundants collected) "abundants" "b" 0
            (encode abundants) (by simpa [boundEnv, setLocal] using getAbundants) rfl pairBody []
            continuation anchors stack (used + 1)
          exact entry.trans (inner.trans completed)
termination_by remaining.length
decreasing_by
  change ((head :: tail).eraseIdx index).length < (head :: tail).length
  rw [List.length_eraseIdx_of_lt bound]
  simp

private abbrev finalTest : Expr := .membership (.name "n") (.name "can") true
private abbrev finalBody : List Stmt := comprehensionFilters [finalTest] (sumBody (.name "n") [])

private theorem final_sum_loop (abundants collected : List Nat) (count start total : Nat)
    (env : HeapCalls.Env) (getCan : env "can" = some (.ref 1))
    (getTotal : env sumAccumulator = some (number total)) :
    BlockReturns program env
      [.rangeStepLoop "n" start (start + count) 1 finalBody [], .return (.name sumAccumulator)]
      (pairHeap abundants collected)
      (number (total + selectedSum (fun n => decide (n ∉ collected)) start count))
      (pairHeap abundants collected) := by
  induction count generalizing start total env with
  | zero =>
      apply BlockReturns.range_done (by simp [Calls.rangeContinues])
      simpa [selectedSum] using BlockReturns.return_value (Evaluates.lookup getTotal)
  | succ count ih =>
      let boundEnv := setLocal env "n" (number start)
      have tested : Evaluates program boundEnv finalTest (pairHeap abundants collected)
          (.scalar (.bool (decide (start ∉ collected)))) (pairHeap abundants collected) := by
        apply Evaluates.membership (.cons (Evaluates.lookup rfl)
          (.cons (Evaluates.lookup (by simpa [boundEnv, setLocal] using getCan)) .nil))
        rw [membership_set _ _ _ _ rfl true, contains_nats]
        simp
      apply BlockReturns.range_step (by simp [Calls.rangeContinues])
      by_cases missing : start ∉ collected
      · apply BlockReturns.branch (flag := true) (by simpa [missing] using tested) rfl
        apply BlockReturns.assign (value := number (total + start)) (middle := pairHeap abundants collected)
        · apply Evaluates.binary (av := number total) (bv := number start)
            (Evaluates.lookup (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal))
            (Evaluates.lookup rfl)
          simp [Mutable.binary, scalarBinary, number]
        · simpa [finalBody, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt, selectedSum, List.range'_succ, missing, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm, Int.add_assoc, Int.add_left_comm, Int.add_comm]
            using ih (start + 1) (total + start) (setLocal boundEnv sumAccumulator (number (total + start)))
              (by simpa [boundEnv, setLocal, sumAccumulator] using getCan) (by simp [setLocal])
      · apply BlockReturns.branch (flag := false) (by simpa [missing] using tested) rfl
        simpa [finalBody, comprehensionFilters, sumBody, Calls.loopContinuation, Calls.loopControl,
            Calls.loopControlStmt, selectedSum, List.range'_succ, missing, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm, Int.add_assoc, Int.add_left_comm, Int.add_comm]
          using ih (start + 1) total boundEnv
            (by simpa [boundEnv, setLocal] using getCan)
            (by simpa [boundEnv, setLocal, sumAccumulator] using getTotal)

private abbrev finalExpression : Expr := .sumRange "n" (.name "n")
  [.constant (.int 1), .binOp (.name "limit") .add (.constant (.int 1))] [finalTest]

private theorem final_sum (limit : Nat) (abundants collected : List Nat) (env : HeapCalls.Env)
    (getLimit : env "limit" = some (number limit)) (getCan : env "can" = some (.ref 1)) :
    Evaluates program env finalExpression (pairHeap abundants collected)
      (number (selectedSum (fun n => decide (n ∉ collected)) 1 limit)) (pairHeap abundants collected) := by
  apply Evaluates.sum_range
  apply Evaluates.sum_generator_range
    (.cons Evaluates.constant (.cons (Evaluates.binary (Evaluates.lookup getLimit) Evaluates.constant rfl) .nil))
    rfl Evaluates.constant rfl
  let sumEnv := setLocal (comprehensionEnv env
    [("n", .call (.name "range") [.constant (.int 1), .binOp (.name "limit") .add (.constant (.int 1))],
      [finalTest])]) sumAccumulator (number 0)
  have executed := final_sum_loop abundants collected limit 1 0 sumEnv
    (by simpa [sumEnv, setLocal, comprehensionEnv, sumAccumulator] using getCan) (by simp [sumEnv, setLocal])
  simpa [Int.add_comm] using executed

private def naiveDefinition : List Arg × List Stmt :=
  (findFunctionIn program.body "naive").getD ([], [])

private theorem naive_pairs (limit : Int) (abundants : List Nat)
    (built : ReturnsValue program "abundant_set" [number limit] [] (.ref 0) [.set (encode abundants)])
    (choices : ChoiceSchedule) :
    ∃ env collected used,
      (∀ n, n ∈ collected ↔ ∃ a ∈ abundants, ∃ b ∈ abundants, a + b = n) ∧
      env "limit" = some (number limit) ∧ env "can" = some (.ref 1) ∧
      SetCalls.Reaches choices program 0
        ⟨⟨.operation (.call "naive") [number limit], [], []⟩, 0⟩
        ⟨⟨.block [.return finalExpression] env, [], pairHeap abundants collected⟩, used⟩ := by
  let initialEnv := functionEnv naiveDefinition.1 naiveDefinition.2 [number limit] []
  let boundEnv := setLocal (setLocal initialEnv "abundants" (.ref 0)) "can" (.ref 1)
  have setup : BlockContinues program initialEnv
      [.assign [.name "abundants"] (.call (.name "abundant_set") [.name "limit"]),
        .assign [.name "can"] (.builtinCall .set [])]
      [] boundEnv (pairHeap abundants []) := by
    apply BlockContinues.append
      (BlockContinues.assign (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) built))
    exact BlockContinues.assign (Evaluates.builtin .nil rfl)
  obtain ⟨env, collected, used, members, preserved, loop⟩ := outer_loop choices abundants abundants [] boundEnv
    rfl rfl [.return finalExpression] 0 [] 0
  refine ⟨env, collected, used, ?_, ?_, ?_, ?_⟩
  · simpa using members
  · rw [preserved "limit" (by decide) (by decide)]
    rfl
  · rw [preserved "can" (by decide) (by decide)]
    rfl
  · apply SetCalls.Reaches.next rfl
    apply (SetCalls.Reaches.of_heap (setup
      [.forIn (.name "a") (.name "abundants") outerBody [], .return finalExpression] 0 []) choices 0).trans
    exact (enter_set choices boundEnv (pairHeap abundants []) "abundants" "a" 0 (encode abundants)
      rfl rfl outerBody [] [.return finalExpression] 0 [] 0).trans loop

/-- The naive Python result is the statement's finite sum for every set traversal. -/
theorem naive.result (limit : Nat) (choices : ChoiceSchedule) :
    ∃ finalHeap, ((SetCalls.call program "naive" [number limit] []).run choices).Finishes
      ⟨.ok (number (ProjectEulerStatements.P23.naive limit)), [], finalHeap, 0⟩ := by
  obtain ⟨env, collected, used, members, getLimit, getCan, path⟩ := naive_pairs limit (abundantItems limit)
    (abundant_set.result limit []) choices
  have membership : ∀ n, n ∈ collected ↔ ProjectEulerStatements.P23.canBeWritten n limit := by
    intro n
    simpa only [abundantItems_mem, ProjectEulerStatements.P23.canBeWritten] using members n
  have sum : selectedSum (fun n => decide (n ∉ collected)) 1 limit = ProjectEulerStatements.P23.naive limit := by
    classical
    have interval := selectedSum_interval (fun n => decide (n ∉ collected)) (limit + 1)
    simpa [ProjectEulerStatements.P23.naive, membership] using interval
  have executed := final_sum limit (abundantItems limit) collected env getLimit getCan
  rw [sum] at executed
  exact ⟨pairHeap (abundantItems limit) collected,
    (path.trans (SetCalls.Reaches.of_heap ((BlockReturns.return_value executed) 0 []) choices used)).finishes
      (.done rfl)⟩

theorem naive.negative (limit : Int) (negative : limit < 0) (choices : ChoiceSchedule) :
    ((SetCalls.call program "naive" [number limit] []).run choices).Finishes
      ⟨.ok (number 0), [], pairHeap [] [], 0⟩ := by
  obtain ⟨env, collected, used, members, getLimit, getCan, path⟩ := naive_pairs limit []
    (abundant_set.negative limit negative []) choices
  have empty : collected = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro n member
    simpa using (members n).mp member
  subst collected
  have executed : Evaluates program env finalExpression (pairHeap [] []) (number 0) (pairHeap [] []) := by
    apply Evaluates.sum_range
    apply Evaluates.sum_generator_range
      (.cons Evaluates.constant (.cons (Evaluates.binary (Evaluates.lookup getLimit) Evaluates.constant rfl) .nil))
      rfl Evaluates.constant rfl
    apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup rfl)
  exact (path.trans (SetCalls.Reaches.of_heap ((BlockReturns.return_value executed) 0 []) choices used)).finishes
    (.done rfl)

theorem naive.«Returns» (limit : Int) :
    (SetCalls.call program "naive" [number limit] []).Returns := by
  intro choices
  by_cases negative : limit < 0
  · exact ⟨number 0, [], pairHeap [] [], 0, naive.negative limit negative choices⟩
  · lift limit to Nat using (by omega : 0 ≤ limit)
    obtain ⟨heap, finished⟩ := naive.result limit choices
    exact ⟨number (ProjectEulerStatements.P23.naive limit), [], heap, 0, finished⟩

theorem naive.«Supported» (limit : Int) :
    (SetCalls.call program "naive" [number limit] []).Supported := by
  intro choices
  exact (naive.«Returns» limit choices).supported

end data.«project-euler-statements».data.py.project_euler_statements.p23
