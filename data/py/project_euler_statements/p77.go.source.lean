import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p77.py.ast»
import lang.py.FormalSW.HeapMemoCallRules
import ProjectEulerStatements.Lib.PrimePartitions

/-! The cached source recurrence counts partitions for arbitrary nonnegative denominations. -/
namespace data.«project-euler-statements».data.py.project_euler_statements.p77
open FormalSW.PyAst HeapMemoCalls
set_option Elab.async false
variable {globals : Mutable.Globals}

abbrev program := P77Ast.module
abbrev integer (n : Int) : Mutable.Value := .scalar (.int n)
abbrev integers (items : List Nat) : List Mutable.Value := items.map (fun n : Nat => integer n)

def ways (n : Int) (coins : List Nat) : Int :=
  if n < 0 then 0 else ProjectEulerStatements.P31.countWaysBound n.toNat coins

theorem ways_zero (coins : List Nat) : ways 0 coins = 1 := by
  simp only [ways, Int.lt_irrefl, ↓reduceIte, Int.toNat_zero]
  rw [ProjectEulerStatements.P31.countWaysBound]
  rfl

theorem ways_nil (n : Int) (nonzero : n ≠ 0) : ways n [] = 0 := by
  by_cases negative : n < 0
  · simp [ways, negative]
  · have positive : 0 < n.toNat := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n.toNat ≠ 0)
    simp only [ways, if_neg negative, hm]
    rw [ProjectEulerStatements.P31.countWaysBound]
    · rfl
    · omega

theorem ways_cons (n : Int) (p : Nat) (coins : List Nat) (nonzero : n ≠ 0) :
    ways n (p :: coins) = if p = 0 then ways n coins else
      (if (p : Int) ≤ n then ways (n-p) (p :: coins) else 0) + ways n coins := by
  by_cases negative : n < 0
  · simp [ways, negative, show ¬ (p : Int) ≤ n by omega]
  · have recurrence : ProjectEulerStatements.P31.countWaysBound n.toNat (p :: coins) =
        if p = 0 then ProjectEulerStatements.P31.countWaysBound n.toNat coins else
        if n.toNat < p then ProjectEulerStatements.P31.countWaysBound n.toNat coins else
          ProjectEulerStatements.P31.countWaysBound (n.toNat-p) (p :: coins) +
            ProjectEulerStatements.P31.countWaysBound n.toNat coins := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n.toNat ≠ 0)
      rw [hm, ProjectEulerStatements.P31.countWaysBound]
      · split <;> simp_all
      · omega
    by_cases zero : p = 0
    · simp only [ways, if_neg negative]
      rw [recurrence]
      simp [zero]
    · by_cases enough : (p : Int) ≤ n
      · have notSmall : ¬ n.toNat < p := by omega
        have subNonnegative : ¬ n - p < 0 := by omega
        have subtract : (n-p).toNat = n.toNat-p := by omega
        simp [ways, negative, zero, enough, subNonnegative, subtract, recurrence, notSmall]
      · have small : n.toNat < p := by omega
        simp [ways, negative, zero, enough, recurrence, small]

def key (n : Int) (coins : List Nat) : Key :=
  ⟨"go", [], some [.scalar (.int n), .tuple (coins.map (fun p : Nat => HashKey.scalar (.int p)))]⟩

def cacheSpec (_heap : Heap) (query : Key) (value : Mutable.Value) : Prop :=
  ∃ n : Int, ∃ coins : List Nat, query = key n coins ∧ value = integer (ways n coins)

theorem cache_preserved (before after : Heap) : Cache.Preserves cacheSpec before after :=
  fun _ valid => valid

theorem cache_unique (n : Int) (coins : List Nat) (value : Mutable.Value)
    (correct : cacheSpec heap (key n coins) value) : value = integer (ways n coins) := by
  obtain ⟨otherN, otherCoins, same, rfl⟩ := correct
  have equal : n = otherN ∧
      coins.map (fun p : Nat => HashKey.scalar (.int (p : Int))) =
        otherCoins.map (fun p : Nat => HashKey.scalar (.int (p : Int))) := by
    simpa [key, MemoCalls.Key.mk.injEq] using same
  have injective : Function.Injective (fun p : Nat => HashKey.scalar (.int (p : Int))) := by
    intro a b same
    have cast : (a : Int) = b := by simpa using same
    omega
  have sameCoins := (List.map_inj_right injective).mp equal.2
  rcases equal with ⟨rfl, _⟩
  subst otherCoins
  rfl

private theorem found_append {heap : Heap} {address : Nat}
    (found : heap[address]? = some (object : Mutable.Object)) (extra : Heap) :
    (heap ++ extra)[address]? = some object := by
  have inside : address < heap.length := by
    by_contra outside
    simp [List.getElem?_eq_none (by omega : heap.length ≤ address)] at found
  rw [List.getElem?_append_left inside]
  exact found

/-- Empty tuples may reuse their canonical wrapper; every other tuple is freshly allocated. -/
theorem tuple_allocation (items : List Mutable.Value) (heap : Heap) :
    ∃ address extra, Mutable.allocateTuple items heap = some (.ok (.ref address), heap ++ extra) ∧
      (heap ++ extra)[address]? = some (.tuple items) := by
  cases items with
  | nil =>
      cases found : heap.findIdx? (fun object => decide (object = .tuple [])) with
      | none =>
          refine ⟨heap.length, [.tuple []], ?_, by simp⟩
          simp [Mutable.allocateTuple, found, Except.map]
      | some address =>
          refine ⟨address, [], ?_, ?_⟩
          · simp [Mutable.allocateTuple, found]
          · have correct := List.of_findIdx?_eq_some found
            cases object : heap[address]? with
            | none => simp [object] at correct
            | some item =>
                have same : item = .tuple [] := by simpa [object] using correct
                simpa [same] using object
  | cons item items =>
      refine ⟨heap.length, [.tuple (item :: items)], ?_, by simp⟩
      simp [Mutable.allocateTuple, Except.map]

private abbrev args := ((findFunctionIn program.body "go").getD ([], [])).1
private abbrev sourceBody := ((findFunctionIn program.body "go").getD ([], [])).2
private abbrev initial (n : Int) (address : Nat) (globals : Mutable.Globals) :=
  HeapCalls.functionEnv args sourceBody [integer n, .ref address] globals

private theorem get_n (n : Int) (address : Nat) : initial n address globals "n" = some (integer n) := by
  cases globals <;> rfl

private theorem get_ps (n : Int) (address : Nat) : initial n address globals "ps" = some (.ref address) := by
  cases globals <;> rfl

private abbrev splitExpression : Expr := .tuple
  [.subscript (.name "ps") (.constant (.int 0)),
    .subscript (.name "ps") (.slice (some (.constant (.int 1))) none none)]

private theorem split_result (n : Int) (p : Nat) (coins : List Nat) (heap : Heap) (address : Nat)
    (found : heap[address]? = some (.tuple (integers (p :: coins)))) :
    ∃ restAddress extra,
      Evaluates (globals := globals) program cacheSpec (initial n address globals) splitExpression heap
        (.ref (heap ++ extra).length)
        ((heap ++ extra) ++ [.tuple [integer p, .ref restAddress]]) ∧
      (heap ++ extra)[restAddress]? = some (.tuple (integers coins)) := by
  obtain ⟨restAddress, extra, allocated, restFound⟩ := tuple_allocation (integers coins) heap
  refine ⟨restAddress, extra, ?_, restFound⟩
  have head : Evaluates (globals := globals) program cacheSpec (initial n address globals)
      (.subscript (.name "ps") (.constant (.int 0))) heap (integer p) heap := by
    apply Evaluates.subscript (ordinary := by intros; simp)
      (Evaluates.lookup (get_ps n address)) Evaluates.constant
    simp [Mutable.getItem, Mutable.index, found, integers, Except.map]
  have tail : Evaluates (globals := globals) program cacheSpec (initial n address globals)
      (.subscript (.name "ps") (.slice (some (.constant (.int 1))) none none)) heap
      (.ref restAddress) (heap ++ extra) := by
    apply Evaluates.slice (.cons (Evaluates.lookup (get_ps n address))
      (.cons Evaluates.constant (.cons Evaluates.constant (.cons Evaluates.constant .nil))))
    have sliced := Mutable.getSlice_tuple_suffix heap address (integers (p :: coins)) 1
      (by omega) (by simp [integers]) found
    simpa [integers] using sliced.trans allocated
  exact Evaluates.tuple (.cons head (.cons tail .nil)) (cache_preserved _ _)

def resultPost (n : Int) (coins : List Nat) (heap : Heap) (value : Mutable.Value) (after : Heap) : Prop :=
  value = integer (ways n coins) ∧ ∃ extra, after = heap ++ extra

private theorem memo_key (n : Int) (coins : List Nat) (heap : Heap) (address : Nat)
    (found : heap[address]? = some (.tuple (integers coins))) :
    memoKey heap "go" [integer n, .ref address] = some (.ok (key n coins)) := by
  simpa [integers, key, List.map_map] using
    memoKey_integer_tuple heap "go" n address (coins.map (fun p : Nat => (p : Int)))
      (by simpa [integers, List.map_map] using found)

private theorem branch
    (evaluated : Evaluates (globals := globals) program cacheSpec env condition heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : BlockReturnsRel (globals := globals) program cacheSpec env
      ((if flag then yes else no) ++ body) middle post) :
    BlockReturnsRel (globals := globals) program cacheSpec env (.ifThen condition yes no :: body) heap post := by
  apply BlockReturnsRel.branch evaluated.rel
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨flag, truth, rest⟩

private theorem conditional
    (evaluated : Evaluates (globals := globals) program cacheSpec env test heap value middle)
    (truth : Mutable.truth value middle = some (.ok flag, middle))
    (rest : EvaluatesRel (globals := globals) program cacheSpec env (if flag then yes else no) middle post) :
    EvaluatesRel (globals := globals) program cacheSpec env (.ifExp test yes no) heap post := by
  apply EvaluatesRel.conditional evaluated.rel
  rintro _ _ ⟨rfl, rfl⟩
  exact ⟨flag, truth, rest⟩

private theorem call
    (arguments : Evaluates.Arguments (globals := globals) program cacheSpec env expressions heap values middle)
    (callee : ReturnsRel (globals := globals) program cacheSpec name values middle post) :
    EvaluatesRel (globals := globals) program cacheSpec env (.call (.name name) expressions) heap post := by
  apply EvaluatesRel.call (ArgumentsRel.fixed arguments)
  rintro _ _ ⟨rfl, rfl⟩
  exact callee

/-- The original tuple-keyed cache executes the recurrence and only appends private objects. -/
theorem go.result (n : Int) (coins : List Nat) (heap : Heap) (address : Nat)
    (found : heap[address]? = some (.tuple (integers coins))) :
    ReturnsRel (globals := globals) program cacheSpec "go" [integer n, .ref address] heap
      (resultPost n coins heap) := by
  induction measure : n.toNat + coins.length using Nat.strong_induction_on
      generalizing n coins heap address with
  | h size ih =>
      have bodyResult : BlockReturnsRel (globals := globals) program cacheSpec
          (initial n address globals) (executableBody sourceBody) heap (resultPost n coins heap) := by
        have zeroTest : Evaluates (globals := globals) program cacheSpec (initial n address globals)
            (.compare (.name "n") [(.eq, .constant (.int 0))]) heap
            (.scalar (.bool (decide (n = 0)))) heap := by
          apply Evaluates.compare (Evaluates.lookup (get_n n address)) Evaluates.constant
          simp [HeapCalls.compare, scalarCompare, evalCmpOp]
        by_cases zero : n = 0
        · apply branch (value := .scalar (.bool true)) (flag := true)
            (by simpa only [zero, decide_true] using zeroTest) rfl
          apply BlockReturnsRel.return_value
          exact EvaluatesRel.constant ⟨by simp [zero, ways_zero], ⟨[], by simp⟩⟩
        · apply branch (value := .scalar (.bool false)) (flag := false)
            (by simpa only [zero, decide_false] using zeroTest) rfl
          cases coins with
          | nil =>
              apply branch (value := .scalar (.bool true)) (flag := true)
              · apply Evaluates.unary (Evaluates.lookup (get_ps n address))
                simp [HeapCalls.unary, Mutable.truth, found, integers]
              · rfl
              · apply BlockReturnsRel.return_value
                exact EvaluatesRel.constant ⟨by simp [ways_nil n zero], ⟨[], by simp⟩⟩
          | cons p coins =>
              obtain ⟨restAddress, extra, split, restFound⟩ := split_result n p coins heap address found
              let middle := (heap ++ extra) ++ [.tuple [integer p, .ref restAddress]]
              let env := HeapCalls.assignNames (initial n address globals) ["p", "rest"] [integer p, .ref restAddress]
              have getN : env "n" = some (integer n) := by
                simpa [env, HeapCalls.assignNames, HeapCalls.setLocal] using get_n (globals := globals) n address
              have getPS : env "ps" = some (.ref address) := by
                simpa [env, HeapCalls.assignNames, HeapCalls.setLocal] using get_ps (globals := globals) n address
              have getP : env "p" = some (integer p) := by simp [env, HeapCalls.assignNames, HeapCalls.setLocal]
              have getRest : env "rest" = some (.ref restAddress) := by simp [env, HeapCalls.assignNames, HeapCalls.setLocal]
              have restAt : middle[restAddress]? = some (.tuple (integers coins)) := found_append restFound _
              have originalAt : middle[address]? = some (.tuple (integers (p :: coins))) :=
                found_append (found_append found _) _
              have enter :
                  BlockReturnsRel (globals := globals) program cacheSpec env
                    ((executableBody sourceBody).drop 3) middle (resultPost n (p :: coins) middle) →
                  BlockReturnsRel (globals := globals) program cacheSpec (initial n address globals)
                    ((executableBody sourceBody).drop 1) heap (resultPost n (p :: coins) heap) := by
                intro rest
                apply branch (value := .scalar (.bool false)) (flag := false)
                · apply Evaluates.unary (Evaluates.lookup (get_ps n address))
                  simp [HeapCalls.unary, Mutable.truth, found, integers]
                · rfl
                · apply BlockReturnsRel.unpack (expressions := [.name "p", .name "rest"])
                    (names := ["p", "rest"]) (items := [integer p, .ref restAddress])
                    (middle := middle) (afterUnpack := middle) rfl split
                  · simp [middle, Mutable.sequence]
                  · rfl
                  · apply rest.consequence
                    rintro value after ⟨same, suffix, rfl⟩
                    exact ⟨same, ⟨extra ++ [.tuple [integer p, .ref restAddress]] ++ suffix,
                      by simp [middle, List.append_assoc]⟩⟩
              apply enter
              have pTest : Evaluates (globals := globals) program cacheSpec env
                  (.compare (.name "p") [(.eq, .constant (.int 0))]) middle
                  (.scalar (.bool (decide (p = 0)))) middle := by
                apply Evaluates.compare (Evaluates.lookup getP) Evaluates.constant
                simp [HeapCalls.compare, scalarCompare, evalCmpOp]
              have rightCall := ih (n.toNat + coins.length)
                (by simp only [List.length_cons] at measure; omega) n coins middle restAddress restAt rfl
              have right : EvaluatesRel (globals := globals) program cacheSpec env
                  (.call (.name "go") [.name "n", .name "rest"]) middle (resultPost n coins middle) :=
                call (.cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getRest) .nil)) rightCall
              by_cases pZero : p = 0
              · apply branch (value := .scalar (.bool true)) (flag := true)
                  (by simpa only [pZero, decide_true] using pTest) rfl
                apply BlockReturnsRel.return_value
                apply right.consequence
                rintro value after ⟨same, suffix, rfl⟩
                refine ⟨?_, suffix, rfl⟩
                rw [ways_cons n p coins zero, if_pos pZero]
                exact same
              · apply branch (value := .scalar (.bool false)) (flag := false)
                  (by simpa only [pZero, decide_false] using pTest) rfl
                have enoughTest : Evaluates (globals := globals) program cacheSpec env
                    (.compare (.name "p") [(.ltE, .name "n")]) middle
                    (.scalar (.bool (decide ((p : Int) ≤ n)))) middle :=
                  Evaluates.compare (Evaluates.lookup getP) (Evaluates.lookup getN) rfl
                apply BlockReturnsRel.return_value
                by_cases enough : (p : Int) ≤ n
                · have leftCall := ih ((n-p).toNat + (p :: coins).length)
                    (by simp only [List.length_cons] at measure ⊢; omega)
                    (n-p) (p :: coins) middle address originalAt rfl
                  have left : EvaluatesRel (globals := globals) program cacheSpec env
                      (.call (.name "go") [.binOp (.name "n") .sub (.name "p"), .name "ps"])
                      middle (resultPost (n-p) (p :: coins) middle) := by
                    apply call _ leftCall
                    exact .cons (Evaluates.binary (Evaluates.lookup getN) (Evaluates.lookup getP) rfl)
                      (.cons (Evaluates.lookup getPS) .nil)
                  apply EvaluatesRel.binary
                    (leftPost := resultPost (n-p) (p :: coins) middle)
                    (rightPost := fun _ after => resultPost n coins after)
                  · exact conditional (value := .scalar (.bool true)) (flag := true)
                      (by simpa only [enough, decide_true] using enoughTest) rfl left
                  · rintro value after ⟨_, suffix, rfl⟩
                    apply call _ (ih (n.toNat + coins.length)
                      (by simp only [List.length_cons] at measure; omega)
                      n coins (middle ++ suffix) restAddress (found_append restAt _) rfl)
                    exact .cons (Evaluates.lookup getN) (.cons (Evaluates.lookup getRest) .nil)
                  · rintro av after bv final ⟨rfl, firstExtra, rfl⟩ ⟨rfl, lastExtra, rfl⟩
                    refine ⟨integer (ways (n-p) (p :: coins) + ways n coins), _, rfl,
                      cache_preserved _ _, ?_, ⟨firstExtra ++ lastExtra, by simp [List.append_assoc]⟩⟩
                    simp [ways_cons n p coins zero, pZero, enough]
                · apply EvaluatesRel.binary
                    (leftPost := fun value after => value = integer 0 ∧ after = middle)
                    (rightPost := fun _ after => resultPost n coins after)
                  · apply conditional (value := .scalar (.bool false)) (flag := false)
                      (by simpa only [enough, decide_false] using enoughTest) rfl
                    exact EvaluatesRel.constant ⟨rfl, rfl⟩
                  · rintro value after ⟨rfl, rfl⟩
                    exact right
                  · rintro av after bv final ⟨rfl, rfl⟩ ⟨rfl, suffix, rfl⟩
                    refine ⟨integer (0 + ways n coins), _, rfl, cache_preserved _ _, ?_, ⟨suffix, rfl⟩⟩
                    simp [ways_cons n p coins zero, pZero, enough]
      apply BlockReturnsRel.memoized_key (key := key n coins) (args := args) (body := sourceBody)
        (by decide) rfl (memo_key n coins heap address found) rfl
      · apply bodyResult.consequence
        intro value after holds
        exact ⟨holds, n, coins, rfl, holds.1⟩
      · intro value correct
        exact ⟨cache_unique n coins value correct, ⟨[], by simp⟩⟩

end data.«project-euler-statements».data.py.project_euler_statements.p77
