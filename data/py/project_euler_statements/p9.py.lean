import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p9.py.ast»
import FormalSW
import ProjectEulerStatements.P9
import Mathlib.Tactic

namespace data.«project-euler-statements».data.py.project_euler_statements.p9
open FormalSW.PyAst
private abbrev program := P9Ast.module
private def ints (items : List Int) := items.map Constant.int
private def insertInt (items : List Int) (value : Int) :=
  if value ∈ items then items else items ++ [value]
private def valid (n a b : Int) : Prop :=
  a < b ∧ b < n - a - b ∧ a * a + b * b = (n - a - b) * (n - a - b)
private instance (n a b : Int) : Decidable (valid n a b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private def collectRow (n a : Int) : Nat → Int → List Int → List Int
  | 0, _, items => items
  | count + 1, b, items => collectRow n a count (b + 1)
      (if valid n a b then insertInt items (a * b * (n - a - b)) else items)
private def collectRows (n : Nat) : Nat → Int → List Int → List Int
  | 0, _, items => items
  | count + 1, a, items => collectRows n count (a + 1) (collectRow n a n 1 items)

private abbrev ordered : Expr :=
  .compare (.name "a") [(.lt, .name "b"), (.lt, .name "c")]
private abbrev square (name : String) : Expr := .binOp (.name name) .mult (.name name)
private abbrev pythagorean : Expr :=
  .compare (.binOp (square "a") .add (square "b")) [(.eq, square "c")]
private abbrev condition : Expr := .boolOp .and [ordered, pythagorean]
private abbrev product : Expr := .binOp (.binOp (.name "a") .mult (.name "b")) .mult (.name "c")
private abbrev innerBody : List Stmt :=
  [.assign [.name "c"] (.binOp (.binOp (.name "n") .sub (.name "a")) .sub (.name "b")),
   .ifThen condition [.expr (.call (.attribute (.name "out") "add") [product])] []]

private theorem ordered.result (env : HeapCalls.Env) (heap : Mutable.Heap) (a b c : Int)
    (ha : env "a" = some (.scalar (.int a))) (hb : env "b" = some (.scalar (.int b)))
    (hc : env "c" = some (.scalar (.int c))) :
    HeapCalls.Evaluates program env ordered heap (.scalar (.bool (decide (a < b ∧ b < c)))) heap := by
  by_cases ab : a < b
  · apply HeapCalls.Evaluates.chain (HeapCalls.Evaluates.lookup ha)
    apply HeapCalls.Evaluates.Compares.next (compared := .scalar (.bool true))
      (afterComparison := heap) (HeapCalls.Evaluates.lookup hb)
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, ab]
    · rfl
    · apply HeapCalls.Evaluates.Compares.last (HeapCalls.Evaluates.lookup hc)
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, ab]
  · apply HeapCalls.Evaluates.chain (HeapCalls.Evaluates.lookup ha)
    apply HeapCalls.Evaluates.Compares.stop (HeapCalls.Evaluates.lookup hb)
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, ab]
    · simp [Mutable.truth, scalarTruth, ab]

private theorem square.result (env : HeapCalls.Env) (heap : Mutable.Heap) (name : String) (value : Int)
    (found : env name = some (.scalar (.int value))) :
    HeapCalls.Evaluates program env (square name) heap (.scalar (.int (value * value))) heap :=
  HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup found) (HeapCalls.Evaluates.lookup found) rfl

private theorem condition.result (env : HeapCalls.Env) (heap : Mutable.Heap) (n a b : Int)
    (ha : env "a" = some (.scalar (.int a))) (hb : env "b" = some (.scalar (.int b)))
    (hc : env "c" = some (.scalar (.int (n - a - b)))) :
    HeapCalls.Evaluates program env condition heap (.scalar (.bool (decide (valid n a b)))) heap := by
  have squares : HeapCalls.Evaluates program env pythagorean heap
      (.scalar (.bool (decide (a * a + b * b = (n - a - b) * (n - a - b))))) heap := by
    apply HeapCalls.Evaluates.compare
      (HeapCalls.Evaluates.binary (square.result env heap "a" a ha) (square.result env heap "b" b hb) rfl)
      (square.result env heap "c" (n - a - b) hc)
    simp [HeapCalls.compare, scalarCompare, evalCmpOp]
  by_cases order : a < b ∧ b < n - a - b
  · apply HeapCalls.Evaluates.boolean_next (value := .scalar (.bool true)) (flag := true)
      (middle := heap)
    · simpa [order] using ordered.result env heap a b (n - a - b) ha hb hc
    · rfl
    · rfl
    · apply HeapCalls.Evaluates.boolean_last (flag := decide (valid n a b))
      · simpa [valid, order.1, order.2] using squares
      · rfl
  · have invalid : ¬valid n a b := fun h => order ⟨h.1, h.2.1⟩
    apply HeapCalls.Evaluates.boolean_stop (flag := false)
    · simpa [invalid, order] using ordered.result env heap a b (n - a - b) ha hb hc
    · simp [Mutable.truth, scalarTruth, invalid]
    · rfl

private theorem innerBody.result (env : HeapCalls.Env) (heap : Mutable.Heap)
    (items : List Int) (n a b : Int)
    (hn : env "n" = some (.scalar (.int n))) (ha : env "a" = some (.scalar (.int a)))
    (hb : env "b" = some (.scalar (.int b))) (hout : env "out" = some (.ref heap.length)) :
    HeapCalls.BlockContinues program env innerBody (heap ++ [.set (ints items)])
      (HeapCalls.setLocal env "c" (.scalar (.int (n - a - b))))
      (heap ++ [.set (ints (if valid n a b then insertInt items (a * b * (n - a - b)) else items))]) := by
  apply HeapCalls.BlockContinues.append
    (HeapCalls.BlockContinues.assign (value := .scalar (.int (n - a - b)))
      (HeapCalls.Evaluates.binary
        (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup hn) (HeapCalls.Evaluates.lookup ha) rfl)
        (HeapCalls.Evaluates.lookup hb) rfl))
  let env' := HeapCalls.setLocal env "c" (.scalar (.int (n - a - b)))
  have getA : env' "a" = some (.scalar (.int a)) := by simpa [env', HeapCalls.setLocal] using ha
  have getB : env' "b" = some (.scalar (.int b)) := by simpa [env', HeapCalls.setLocal] using hb
  have getC : env' "c" = some (.scalar (.int (n - a - b))) := rfl
  have getOut : env' "out" = some (.ref heap.length) := by simpa [env', HeapCalls.setLocal] using hout
  have guard := condition.result env' (heap ++ [.set (ints items)]) n a b getA getB getC
  by_cases good : valid n a b
  · apply HeapCalls.BlockContinues.branch (flag := true) (value := .scalar (.bool true))
    · simpa [good] using guard
    · rfl
    · apply HeapCalls.BlockContinues.discard (value := .scalar .none)
      have found : (heap ++ [.set (ints items)])[heap.length]? = some (.set (ints items)) := by simp
      have prod : HeapCalls.Evaluates program env' product (heap ++ [.set (ints items)])
          (.scalar (.int (a * b * (n - a - b)))) (heap ++ [.set (ints items)]) :=
        HeapCalls.Evaluates.binary
          (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getA) (HeapCalls.Evaluates.lookup getB) rfl)
          (HeapCalls.Evaluates.lookup getC) rfl
      have inserted := HeapCalls.Evaluates.add (HeapCalls.Evaluates.lookup getOut) found prod found
      simpa [good, ints, ScalarSet.insert_ints, insertInt] using inserted
  · apply HeapCalls.BlockContinues.branch (flag := false) (value := .scalar (.bool false))
    · simpa [good] using guard
    · rfl
    · simpa [good] using (HeapCalls.BlockContinues.nil (module := program) (env := env')
        (heap := heap ++ [.set (ints items)]))

private theorem row.result (count : Nat) (n a b : Int) (bound : n + 1 = b + count)
    (env : HeapCalls.Env) (heap : Mutable.Heap) (items : List Int)
    (hn : env "n" = some (.scalar (.int n))) (ha : env "a" = some (.scalar (.int a)))
    (hout : env "out" = some (.ref heap.length)) :
    ∃ finalEnv, HeapCalls.BlockContinues program env
      [.rangeStepLoop "b" b (n + 1) 1 innerBody []] (heap ++ [.set (ints items)])
      finalEnv (heap ++ [.set (ints (collectRow n a count b items))]) ∧
      finalEnv "n" = some (.scalar (.int n)) ∧ finalEnv "a" = some (.scalar (.int a)) ∧
      finalEnv "out" = some (.ref heap.length) := by
  induction count generalizing b env items with
  | zero =>
      refine ⟨env, ?_, hn, ha, hout⟩
      apply HeapCalls.BlockContinues.range_done
      · simp [Calls.rangeContinues]; omega
      · exact HeapCalls.BlockContinues.nil
  | succ count ih =>
      let envB := HeapCalls.setLocal env "b" (.scalar (.int b))
      let envC := HeapCalls.setLocal envB "c" (.scalar (.int (n - a - b)))
      let updated := if valid n a b then insertInt items (a * b * (n - a - b)) else items
      have getN : envB "n" = some (.scalar (.int n)) := by simpa [envB, HeapCalls.setLocal] using hn
      have getA : envB "a" = some (.scalar (.int a)) := by simpa [envB, HeapCalls.setLocal] using ha
      have getOut : envB "out" = some (.ref heap.length) := by simpa [envB, HeapCalls.setLocal] using hout
      have iteration := innerBody.result envB heap items n a b getN getA rfl getOut
      obtain ⟨finalEnv, next, finalN, finalA, finalOut⟩ := ih (b + 1) (by omega) envC updated
        (by simpa [envC, HeapCalls.setLocal] using getN)
        (by simpa [envC, HeapCalls.setLocal] using getA)
        (by simpa [envC, HeapCalls.setLocal] using getOut)
      refine ⟨finalEnv, ?_, finalN, finalA, finalOut⟩
      apply HeapCalls.BlockContinues.range_step
      · simp [Calls.rangeContinues]; omega
      · simpa only [innerBody, Calls.loopContinuation, Calls.loopControl, Calls.loopControlStmt,
          collectRow] using iteration.append next

private abbrev outerBody : List Stmt :=
  [.forIn (.name "b") (.call (.name "range") [.constant (.int 1),
    .binOp (.name "n") .add (.constant (.int 1))]) innerBody []]

private theorem rows.result (n count : Nat) (a : Int) (bound : (n : Int) + 1 = a + count)
    (env : HeapCalls.Env) (heap : Mutable.Heap) (items : List Int)
    (hn : env "n" = some (.scalar (.int n))) (hout : env "out" = some (.ref heap.length)) :
    ∃ finalEnv, HeapCalls.BlockContinues program env
      [.rangeStepLoop "a" a (n + 1) 1 outerBody []] (heap ++ [.set (ints items)])
      finalEnv (heap ++ [.set (ints (collectRows n count a items))]) ∧
      finalEnv "n" = some (.scalar (.int n)) ∧ finalEnv "out" = some (.ref heap.length) := by
  induction count generalizing a env items with
  | zero =>
      refine ⟨env, ?_, hn, hout⟩
      apply HeapCalls.BlockContinues.range_done
      · simp [Calls.rangeContinues]; omega
      · exact HeapCalls.BlockContinues.nil
  | succ count ih =>
      let envA := HeapCalls.setLocal env "a" (.scalar (.int a))
      have getN : envA "n" = some (.scalar (.int n)) := by simpa [envA, HeapCalls.setLocal] using hn
      have getOut : envA "out" = some (.ref heap.length) := by simpa [envA, HeapCalls.setLocal] using hout
      obtain ⟨rowEnv, row, rowN, _, rowOut⟩ := row.result n n a 1 (by omega) envA heap items getN rfl getOut
      have iteration : HeapCalls.BlockContinues program envA outerBody (heap ++ [.set (ints items)])
          rowEnv (heap ++ [.set (ints (collectRow n a n 1 items))]) := by
        apply HeapCalls.BlockContinues.for_range
          (.cons HeapCalls.Evaluates.constant (.cons
            (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup getN) HeapCalls.Evaluates.constant rfl) .nil))
          rfl row
      obtain ⟨finalEnv, next, finalN, finalOut⟩ := ih (a + 1) (by omega) rowEnv
        (collectRow n a n 1 items) rowN rowOut
      refine ⟨finalEnv, ?_, finalN, finalOut⟩
      apply HeapCalls.BlockContinues.range_step
      · simp [Calls.rangeContinues]; omega
      · simpa only [outerBody, innerBody, Calls.loopContinuation, Calls.loopControl,
          Calls.loopControlStmt, collectRows] using iteration.append next

def products (n : Nat) : List Int := collectRows n n 1 []

private theorem mem_insertInt (items : List Int) (x value : Int) :
    value ∈ insertInt items x ↔ value ∈ items ∨ value = x := by
  unfold insertInt
  split
  · rename_i present
    constructor
    · exact Or.inl
    · rintro (member | rfl)
      · exact member
      · exact present
  · simp

private theorem interval_split (b : Int) (count : Nat) (predicate : Int → Prop) :
    (∃ x, b ≤ x ∧ x < b + (count + 1 : Nat) ∧ predicate x) ↔
      predicate b ∨ ∃ x, b + 1 ≤ x ∧ x < b + 1 + count ∧ predicate x := by
  constructor
  · rintro ⟨x, lower, upper, property⟩
    by_cases same : x = b
    · exact .inl (same ▸ property)
    · exact .inr ⟨x, by omega, by omega, property⟩
  · rintro (property | ⟨x, lower, upper, property⟩)
    · exact ⟨b, le_rfl, by omega, property⟩
    · exact ⟨x, by omega, by omega, property⟩

private theorem collectRow.mem (n a : Int) (count : Nat) (b value : Int) (items : List Int) :
    value ∈ collectRow n a count b items ↔ value ∈ items ∨
      ∃ x, b ≤ x ∧ x < b + count ∧ valid n a x ∧ value = a * x * (n - a - x) := by
  induction count generalizing b items with
  | zero =>
      simp [collectRow]
      intro x lower upper
      omega
  | succ count ih =>
      simp only [collectRow, ih]
      rw [interval_split]
      by_cases good : valid n a b
      · simp [good, mem_insertInt, or_assoc]
      · simp [good]

private theorem collectRows.mem (n count : Nat) (a value : Int) (items : List Int) :
    value ∈ collectRows n count a items ↔ value ∈ items ∨
      ∃ x, a ≤ x ∧ x < a + count ∧
        ∃ y : Int, 1 ≤ y ∧ y < 1 + n ∧ valid n x y ∧ value = x * y * (n - x - y) := by
  induction count generalizing a items with
  | zero =>
      simp [collectRows]
      intro x lower upper
      omega
  | succ count ih =>
      simp only [collectRows, ih, collectRow.mem]
      rw [interval_split]
      exact or_assoc

/-- The source visits every ordered pair in the two Python ranges. -/
theorem products.mem (n : Nat) (value : Int) :
    value ∈ products n ↔ ∃ a b : Int,
      1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n ∧ valid n a b ∧ value = a * b * (n - a - b) := by
  simp only [products, collectRows.mem, List.not_mem_nil, false_or]
  constructor
  · rintro ⟨a, lowerA, upperA, b, lowerB, upperB, good, value⟩
    exact ⟨a, b, lowerA, by omega, lowerB, by omega, good, value⟩
  · rintro ⟨a, b, lowerA, upperA, lowerB, upperB, good, value⟩
    exact ⟨a, lowerA, by omega, b, lowerB, by omega, good, value⟩

private theorem valid_cast (n a b : Nat) (bound : a + b ≤ n) :
    valid n a b ↔ a < b ∧ b < n - a - b ∧ a ^ 2 + b ^ 2 = (n - a - b) ^ 2 := by
  have boundA : a ≤ n := by omega
  have boundB : b ≤ n - a := by omega
  unfold valid
  rw [← Int.natCast_sub boundA, ← Int.natCast_sub boundB]
  norm_cast
  simp [pow_two]

/-- Canonical source products agree with the existing finite-set specification. -/
theorem products.specification (n : Nat) :
    (products n).toFinset = (ProjectEulerStatements.P9.tripletProducts n).image Int.ofNat := by
  ext value
  rw [List.mem_toFinset, products.mem, Finset.mem_image]
  constructor
  · rintro ⟨a, b, lowerA, upperA, lowerB, upperB, good, rfl⟩
    have castA : (a.toNat : Int) = a := Int.toNat_of_nonneg (by omega)
    have castB : (b.toNat : Int) = b := Int.toNat_of_nonneg (by omega)
    have bound : a.toNat + b.toNat ≤ n := by
      have ordered := good.2.1
      omega
    have goodNat : a.toNat < b.toNat ∧ b.toNat < n - a.toNat - b.toNat ∧
        a.toNat ^ 2 + b.toNat ^ 2 = (n - a.toNat - b.toNat) ^ 2 :=
      (valid_cast n a.toNat b.toNat bound).mp (by simpa [castA, castB] using good)
    refine ⟨a.toNat * b.toNat * (n - a.toNat - b.toNat), ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨(a.toNat, b.toNat), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, goodNat⟩
      simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
      omega
    · have boundA : a.toNat ≤ n := by omega
      have boundB : b.toNat ≤ n - a.toNat := by omega
      simp [Int.natCast_sub boundA, Int.natCast_sub boundB, castA, castB]
  · rintro ⟨value, specMember, rfl⟩
    obtain ⟨⟨a, b⟩, pairMember, productEqual⟩ := Finset.mem_image.mp specMember
    obtain ⟨bounds, good⟩ := Finset.mem_filter.mp pairMember
    obtain ⟨⟨lowerA, upperA⟩, ⟨lowerB, upperB⟩⟩ :=
      (by simpa only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc] using bounds)
    have good : a < b ∧ b < n - a - b ∧ a ^ 2 + b ^ 2 = (n - a - b) ^ 2 := good
    have bound : a + b ≤ n := by omega
    have boundB : b ≤ n - a := by omega
    refine ⟨a, b, by omega, by omega, by omega, by omega, (valid_cast n a b bound).mpr good, ?_⟩
    rw [← productEqual]
    simp [Int.natCast_sub upperA, Int.natCast_sub boundB]

theorem triplet_products.result (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "triplet_products" [.scalar (.int n)] heap (.ref heap.length)
      (heap ++ [.set (ints (products n))]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign (value := .ref heap.length) (middle := heap ++ [.set []])
  · exact HeapCalls.Evaluates.builtin .nil (by simp [HeapCalls.primitive, Mutable.allocateSet, Except.map])
  · apply HeapCalls.BlockReturns.for_range
      (.cons HeapCalls.Evaluates.constant (.cons
        (HeapCalls.Evaluates.binary (HeapCalls.Evaluates.lookup rfl) HeapCalls.Evaluates.constant rfl) .nil)) rfl
    let env := HeapCalls.setLocal
      (HeapCalls.argumentEnv [{name := "n", annotation := some (.name "int")}] [.scalar (.int n)])
      "out" (.ref heap.length)
    obtain ⟨finalEnv, run, _, finalOut⟩ := rows.result n n 1 (by omega) env heap [] rfl rfl
    exact run.returns (HeapCalls.BlockReturns.return_value (HeapCalls.Evaluates.lookup finalOut))

theorem triplet_products.«Returns» (n : Int) (requires : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) P9Ast.requires_triplet_products_0) :
    (HeapCalls.call program "triplet_products" [.scalar (.int n)] []).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare requires rfl
  simpa [Int.toNat_of_nonneg nonnegative] using (triplet_products.result n.toNat []).returns

theorem triplet_products.«Supported» (n : Int) (requires : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) P9Ast.requires_triplet_products_0) :
    (HeapCalls.call program "triplet_products" [.scalar (.int n)] []).Supported :=
  (triplet_products.«Returns» n requires).supported

private theorem maximum.result (env : HeapCalls.Env) (heap : Mutable.Heap) (address : Nat)
    (first : Int) (rest : List Int) (found : heap[address]? = some (.set (ints (first :: rest))))
    (lookup : env "vals" = some (.ref address)) :
    HeapCalls.Evaluates program env (.builtinCall .max [.name "vals"]) heap
      (.scalar (.int (rest.foldl max first))) heap := by
  apply HeapCalls.Evaluates.builtin (.cons (HeapCalls.Evaluates.lookup lookup) .nil)
  simp [HeapCalls.primitive, found, ints, ScalarSet.maximum, HeapCalls.scalarResult,
    ScalarSet.maximumFrom_ints, List.mapM_map, List.mapM_pure, Function.comp_def]

private def largest : List Int → Int
  | [] => 0
  | first :: rest => rest.foldl max first

private theorem largest_mem (items : List Int) (nonempty : items ≠ []) : largest items ∈ items := by
  cases items with
  | nil => contradiction
  | cons first rest => exact List.max?_mem (by rfl)

private theorem le_largest (items : List Int) (value : Int) (member : value ∈ items) :
    value ≤ largest items := by
  cases items with
  | nil => simp at member
  | cons first rest => exact List.le_max_of_mem member

private theorem largest_specification (n : Nat) :
    largest (products n) = (ProjectEulerStatements.P9.naive n : Int) := by
  by_cases nonempty : (ProjectEulerStatements.P9.tripletProducts n).Nonempty
  · have listNonempty : products n ≠ [] := by
      intro empty
      obtain ⟨value, member⟩ := nonempty
      have mapped : (value : Int) ∈ (products n).toFinset := by
        rw [products.specification]
        exact Finset.mem_image.mpr ⟨value, member, rfl⟩
      simp [empty] at mapped
    have chosen : largest (products n) ∈ (ProjectEulerStatements.P9.tripletProducts n).image Int.ofNat := by
      rw [← products.specification, List.mem_toFinset]
      exact largest_mem _ listNonempty
    obtain ⟨value, member, equal⟩ := Finset.mem_image.mp chosen
    rw [ProjectEulerStatements.P9.naive, dif_pos nonempty]
    apply le_antisymm
    · calc
        largest (products n) = (value : Int) := equal.symm
        _ ≤ _ := Int.ofNat_le.mpr (Finset.le_max' _ value member)
    · apply le_largest
      apply List.mem_toFinset.mp
      rw [products.specification]
      exact Finset.mem_image.mpr ⟨_, Finset.max'_mem _ nonempty, rfl⟩
  · have empty : products n = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro value member
      have mapped : value ∈ (ProjectEulerStatements.P9.tripletProducts n).image Int.ofNat := by
        rw [← products.specification, List.mem_toFinset]
        exact member
      obtain ⟨value, member, _⟩ := Finset.mem_image.mp mapped
      exact nonempty ⟨value, member⟩
    simp [empty, largest, ProjectEulerStatements.P9.naive, nonempty]

theorem naive.result (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "naive" [.scalar (.int n)] heap
      (.scalar (.int (largest (products n)))) (heap ++ [.set (ints (products n))]) := by
  apply HeapCalls.BlockReturns.function rfl rfl
  apply HeapCalls.BlockReturns.assign
    (HeapCalls.Evaluates.call (.cons (HeapCalls.Evaluates.lookup rfl) .nil) (triplet_products.result n heap))
  apply HeapCalls.BlockReturns.return_value
  cases casesProducts : products n with
  | nil =>
      apply HeapCalls.Evaluates.conditional (flag := false) (HeapCalls.Evaluates.lookup rfl)
      · simp [Mutable.truth, ints]
      · exact HeapCalls.Evaluates.constant
  | cons first rest =>
      apply HeapCalls.Evaluates.conditional (flag := true) (HeapCalls.Evaluates.lookup rfl)
      · simp [Mutable.truth, ints]
      · exact maximum.result _ _ heap.length first rest (by simp) rfl

/-- Reuse the established mathematical specification without replacing Python execution. -/
theorem naive.naturals (n : Nat) (heap : Mutable.Heap) :
    HeapCalls.ReturnsValue program "naive" [.scalar (.int n)] heap
      (.scalar (.int (ProjectEulerStatements.P9.naive n))) (heap ++ [.set (ints (products n))]) := by
  simpa only [largest_specification] using naive.result n heap

theorem naive.«Returns» (n : Int) (requires : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) P9Ast.requires_naive_0) :
    (HeapCalls.scalarFunction program "naive" [.int n]).Returns := by
  have nonnegative : 0 ≤ n := by
    simpa [evalCmpOp] using Calls.Evaluates.condition_int_compare requires rfl
  simpa [Int.toNat_of_nonneg nonnegative] using
    HeapCalls.ReturnsValue.scalar_returns (values := [.int n.toNat]) (naive.result n.toNat [])

theorem naive.«Supported» (n : Int) (requires : Calls.Condition program
    (fun key => if key = "n" then some (.int n) else none) P9Ast.requires_naive_0) :
    (HeapCalls.scalarFunction program "naive" [.int n]).Supported :=
  (naive.«Returns» n requires).supported

end data.«project-euler-statements».data.py.project_euler_statements.p9
