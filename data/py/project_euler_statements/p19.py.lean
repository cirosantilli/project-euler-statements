import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p19.py.ast»
import FormalSW
import ProjectEulerStatements.Lib.Calendar

namespace data.«project-euler-statements».data.py.project_euler_statements.p19
open FormalSW.PyAst
section
open FormalSW.PyAst.Calls
open ProjectEulerStatements.P19 (isLeapInt)

/-- The original short-circuiting expression returns the leap-year predicate. -/
theorem is_leap.result (year : Int) :
    ReturnsValue P19Ast.module "is_leap" [.int year] (.bool (isLeapInt year)) := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  by_cases fourth : year % 4 = 0
  · simp only [isLeapInt, fourth, decide_true, Bool.true_and]
    apply Evaluates.boolean_continue (first := .bool true)
    · apply Evaluates.compare (av := .int (year % 4)) (bv := .int 0)
        (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary]))
        Evaluates.constant
      simp [scalarCompare, evalCmpOp, fourth]
    · rfl
    · apply Evaluates.boolean_last
      by_cases hundred : year % 100 = 0
      · simp only [hundred, ne_eq, not_true_eq_false, decide_false, Bool.false_or]
        apply Evaluates.boolean_continue (first := .bool false)
        · apply Evaluates.compare (av := .int (year % 100)) (bv := .int 0)
            (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary]))
            Evaluates.constant
          simp [scalarCompare, evalCmpOp, hundred]
        · rfl
        · apply Evaluates.boolean_last
          apply Evaluates.compare (av := .int (year % 400)) (bv := .int 0)
            (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary]))
            Evaluates.constant
          simp [scalarCompare, evalCmpOp]
      · simp only [hundred, ne_eq, not_false_eq_true, decide_true, Bool.true_or]
        apply Evaluates.boolean_stop (value := .bool true)
        · apply Evaluates.compare (av := .int (year % 100)) (bv := .int 0)
            (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary]))
            Evaluates.constant
          simp [scalarCompare, evalCmpOp, hundred]
        · rfl
  · simp only [isLeapInt, fourth, decide_false, Bool.false_and]
    apply Evaluates.boolean_stop (value := .bool false)
    · apply Evaluates.compare (av := .int (year % 4)) (bv := .int 0)
        (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant (by simp [scalarBinary]))
        Evaluates.constant
      simp [scalarCompare, evalCmpOp, fourth]
    · rfl

theorem is_leap.«Returns» (year : Int) :
    (Calls.function P19Ast.module "is_leap" [.int year]).Returns := (is_leap.result year).returns

end

open FormalSW.PyAst.HeapCalls
open ProjectEulerStatements.P19 (isLeapInt)
private abbrev program := P19Ast.module

/-- The original short-circuiting expression returns the leap-year predicate. -/
theorem is_leap.heap_result (year : Int) (heap : Mutable.Heap) :
    ReturnsValue program "is_leap" [.scalar (.int year)] heap (.scalar (.bool (isLeapInt year))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  by_cases fourth : year % 4 = 0
  · simp only [isLeapInt, fourth, decide_true, Bool.true_and]
    apply Evaluates.boolean_next (middle := heap) (value := .scalar (.bool true))
    · apply Evaluates.compare (middle := heap) (afterRight := heap) (av := .scalar (.int (year % 4))) (bv := .scalar (.int 0))
        (Evaluates.binary (finalHeap := heap) (Evaluates.lookup rfl) Evaluates.constant (by simp [Mutable.binary, scalarBinary]))
        Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, fourth]
    · rfl
    · rfl
    · apply Evaluates.boolean_last
      by_cases hundred : year % 100 = 0
      · simp only [hundred, ne_eq, not_true_eq_false, decide_false, Bool.false_or]
        apply Evaluates.boolean_next (middle := heap) (value := .scalar (.bool false))
        · apply Evaluates.compare (middle := heap) (afterRight := heap) (av := .scalar (.int (year % 100))) (bv := .scalar (.int 0))
            (Evaluates.binary (finalHeap := heap) (Evaluates.lookup rfl) Evaluates.constant (by simp [Mutable.binary, scalarBinary]))
            Evaluates.constant
          simp [HeapCalls.compare, scalarCompare, evalCmpOp, hundred]
        · rfl
        · rfl
        · apply Evaluates.boolean_last (flag := decide (year % 400 = 0))
          · apply Evaluates.compare (middle := heap) (afterRight := heap)
              (av := .scalar (.int (year % 400))) (bv := .scalar (.int 0))
              (Evaluates.binary (finalHeap := heap) (Evaluates.lookup rfl) Evaluates.constant
                (by simp [Mutable.binary, scalarBinary])) Evaluates.constant
            simp [HeapCalls.compare, scalarCompare, evalCmpOp]
          · rfl
      · simp only [hundred, ne_eq, not_false_eq_true, decide_true, Bool.true_or]
        apply Evaluates.boolean_stop (value := .scalar (.bool true))
        · apply Evaluates.compare (middle := heap) (afterRight := heap) (av := .scalar (.int (year % 100))) (bv := .scalar (.int 0))
            (Evaluates.binary (finalHeap := heap) (Evaluates.lookup rfl) Evaluates.constant (by simp [Mutable.binary, scalarBinary]))
            Evaluates.constant
          simp [HeapCalls.compare, scalarCompare, evalCmpOp, hundred]
        · rfl
        · rfl
      rfl
  · simp only [isLeapInt, fourth, decide_false, Bool.false_and]
    apply Evaluates.boolean_stop (value := .scalar (.bool false))
    · apply Evaluates.compare (middle := heap) (afterRight := heap) (av := .scalar (.int (year % 4))) (bv := .scalar (.int 0))
        (Evaluates.binary (finalHeap := heap) (Evaluates.lookup rfl) Evaluates.constant (by simp [Mutable.binary, scalarBinary]))
        Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, fourth]
    · rfl
    · rfl

open ProjectEulerStatements.P19 (daysInYearInt daysInMonthInt daysBeforeMonthInt)

/-- The helper does not allocate or modify its caller's heap. -/
theorem days_in_year.heap_result (year : Int) (heap : Mutable.Heap) :
    ReturnsValue program "days_in_year" [.scalar (.int year)] heap
      (.scalar (.int (daysInYearInt year))) heap := by
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (flag := isLeapInt year)
    (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) (is_leap.heap_result year heap)) rfl
  cases leap : isLeapInt year <;> simpa [daysInYearInt, leap] using
    (Evaluates.constant (module := program) (env := _) (heap := heap) (value := .int _))

private abbrev monthValues (year : Int) : List Mutable.Value :=
  ([0, 31, if isLeapInt year then 29 else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31] : List Int).map
    (fun n => .scalar (.int n))

private abbrev monthTest : Expr :=
  .compare (.constant (.int 1)) [(.ltE, .name "m"), (.ltE, .constant (.int 12))]

private theorem monthTest.result (month : Int) (env : Mutable.Env) (heap : Mutable.Heap)
    (lookup : env "m" = some (.scalar (.int month))) :
    Evaluates program env monthTest heap (.scalar (.bool (decide (1 ≤ month ∧ month ≤ 12)))) heap := by
  by_cases lower : 1 ≤ month
  · apply Evaluates.chain Evaluates.constant
    apply Evaluates.Compares.next (value := .scalar (.int month)) (compared := .scalar (.bool true))
      (afterComparison := heap) (Evaluates.lookup lookup)
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
    · rfl
    · apply Evaluates.Compares.last (middle := heap) Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
  · simp only [lower, false_and, decide_false]
    apply Evaluates.chain Evaluates.constant
    apply Evaluates.Compares.stop (middle := heap) (Evaluates.lookup lookup)
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
    · rfl

private abbrev monthList : Expr := .list
  [.constant (.int 0), .constant (.int 31),
    .ifExp (.call (.name "is_leap") [.name "y"]) (.constant (.int 29)) (.constant (.int 28)),
    .constant (.int 31), .constant (.int 30), .constant (.int 31), .constant (.int 30),
    .constant (.int 31), .constant (.int 31), .constant (.int 30), .constant (.int 31),
    .constant (.int 30), .constant (.int 31)]

private theorem monthList.result (year : Int) (env : Mutable.Env) (heap : Mutable.Heap)
    (lookup : env "y" = some (.scalar (.int year))) :
    Evaluates program env monthList heap (.ref heap.length) (heap ++ [.list (monthValues year)]) := by
  apply Evaluates.list
  refine .cons .constant (.cons .constant (Evaluates.Arguments.cons (middle := heap) ?_ ?_))
  · apply Evaluates.conditional (flag := isLeapInt year)
      (Evaluates.call (.cons (Evaluates.lookup lookup) .nil) (is_leap.heap_result year heap)) rfl
    cases leap : isLeapInt year <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      exact Evaluates.constant
  · repeat' first | exact Evaluates.Arguments.nil | apply Evaluates.Arguments.cons Evaluates.constant

/-- An in-range month allocates precisely the list literal used by the source. -/
theorem days_in_month.valid (year : Int) (month : Nat) (positive : 0 < month) (bound : month ≤ 12)
    (heap : Mutable.Heap) :
    ReturnsValue program "days_in_month" [.scalar (.int year), .scalar (.int month)] heap
      (.scalar (.int (daysInMonthInt year month))) (heap ++ [.list (monthValues year)]) := by
  let env := functionEnv
    [{name := "y", annotation := some (.name "int")}, {name := "m", annotation := some (.name "int")}]
    ((findFunctionIn program.body "days_in_month").getD ([], [])).2
    [.scalar (.int year), .scalar (.int month)] []
  have test := monthTest.result (month : Int) env heap rfl
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (middle := heap) (flag := true) (value := .scalar (.bool true))
  · simpa [monthTest, show 1 ≤ month by omega, bound] using test
  · rfl
  · apply Evaluates.subscript (by intros; simp) (monthList.result year _ heap rfl)
      (Evaluates.lookup rfl)
    have found : (heap ++ [.list (monthValues year)])[heap.length]? = some (.list (monthValues year)) := by simp
    have inside : month < (monthValues year).length := by simpa [monthValues] using (by omega : month < 13)
    have indexed := Mutable.getItem_list (heap ++ [.list (monthValues year)]) heap.length month
      (monthValues year) found inside
    rw [indexed]
    congr 3
    interval_cases month <;> simp [monthValues, daysInMonthInt]

/-- Outside the guard, Python returns zero without allocating the month table. -/
theorem days_in_month.invalid (year month : Int) (outside : month < 1 ∨ 12 < month)
    (heap : Mutable.Heap) :
    ReturnsValue program "days_in_month" [.scalar (.int year), .scalar (.int month)] heap
      (.scalar (.int 0)) heap := by
  let env := functionEnv
    [{name := "y", annotation := some (.name "int")}, {name := "m", annotation := some (.name "int")}]
    ((findFunctionIn program.body "days_in_month").getD ([], [])).2
    [.scalar (.int year), .scalar (.int month)] []
  have test := monthTest.result month env heap rfl
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.conditional (middle := heap) (flag := false) (value := .scalar (.bool false))
  · simpa only [monthTest, show ¬ (1 ≤ month ∧ month ≤ 12) by omega, decide_false] using test
  · rfl
  · exact Evaluates.constant

theorem days_in_month.heap_result (year month : Int) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "days_in_month" [.scalar (.int year), .scalar (.int month)] heap
      (.scalar (.int (daysInMonthInt year month))) (heap ++ extra) := by
  by_cases inside : 1 ≤ month ∧ month ≤ 12
  · lift month to Nat using (by omega : 0 ≤ month)
    exact ⟨[.list (monthValues year)], days_in_month.valid year month (by omega) (by omega) heap⟩
  · refine ⟨[], ?_⟩
    simpa only [List.append_nil, ProjectEulerStatements.P19.daysInMonthInt_outside year month (by omega)] using
      days_in_month.invalid year month (by omega) heap

/-- A finite generator sum preserves existing objects while collecting its allocations. -/
private theorem calendarSum.loop (element : Expr) (number : Nat → Int) (invariant : Mutable.Env → Prop)
    (preserved : ∀ env name value, invariant env →
      (name = "i" ∨ name = sumAccumulator) → invariant (setLocal env name value))
    (evaluated : ∀ heap env (i : Nat), invariant env → env "i" = some (.scalar (.int i)) →
      ∃ extra, Evaluates program env element heap (.scalar (.int (number i))) (heap ++ extra))
    (count first : Nat) (initial : Int) (heap : Mutable.Heap) (env : Mutable.Env)
    (holds : invariant env) (accumulator : env sumAccumulator = some (.scalar (.int initial))) :
    ∃ extra, BlockReturns program env
      [.rangeStepLoop "i" (first : Int) ((first + count : Nat) : Int) 1 (sumBody element []) [],
        .return (.name sumAccumulator)] heap
      (.scalar (.int (initial + ((List.range' first count).map number).sum))) (heap ++ extra) := by
  induction count generalizing first initial heap env with
  | zero =>
      refine ⟨[], ?_⟩
      simp only [Nat.add_zero, List.range'_zero, List.map_nil, List.sum_nil, Int.add_zero, List.append_nil]
      apply BlockReturns.range_done (by simp [Calls.rangeContinues])
      exact BlockReturns.return_value (Evaluates.lookup accumulator)
  | succ count ih =>
      let withI := setLocal env "i" (.scalar (.int first))
      let nextEnv := setLocal withI sumAccumulator (.scalar (.int (initial + number first)))
      have withIHolds : invariant withI := preserved env "i" _ holds (.inl rfl)
      have nextHolds : invariant nextEnv := preserved withI sumAccumulator _ withIHolds (.inr rfl)
      obtain ⟨allocated, term⟩ := evaluated heap withI first withIHolds (by simp [withI, setLocal])
      obtain ⟨later, continued⟩ := ih (first + 1) (initial + number first)
        (heap ++ allocated) nextEnv nextHolds (by simp [nextEnv, setLocal])
      refine ⟨allocated ++ later, ?_⟩
      apply BlockReturns.range_step (by simp [Calls.rangeContinues])
      apply BlockReturns.assign (value := .scalar (.int (initial + number first))) (middle := heap ++ allocated)
      · apply Evaluates.binary
          (Evaluates.lookup (by simpa [setLocal, sumAccumulator] using accumulator)) term
        rfl
      · change BlockReturns program nextEnv
          [.rangeStepLoop "i" ((first : Int) + 1) ((first + (count + 1) : Nat) : Int) 1 (sumBody element []) [],
            .return (.name sumAccumulator)] (heap ++ allocated) _ _
        simpa only [List.range'_succ, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Int.add_assoc, Int.add_left_comm, Int.add_comm,
          List.append_assoc] using continued

private abbrev yearElement : Expr :=
  .call (.name "days_in_year") [.binOp (.constant (.int 1900)) .add (.name "i")]

private theorem yearElement.result (heap : Mutable.Heap) (env : Mutable.Env) (i : Nat)
    (lookup : env "i" = some (.scalar (.int i))) :
    Evaluates program env yearElement heap
      (.scalar (.int (ProjectEulerStatements.P19.daysInYear (1900 + i)))) heap := by
  have called := days_in_year.heap_result ((1900 + i : Nat) : Int) heap
  rw [ProjectEulerStatements.P19.daysInYearInt_nat] at called
  apply Evaluates.call _ called
  apply Evaluates.Arguments.cons _ .nil
  exact Evaluates.binary Evaluates.constant (Evaluates.lookup lookup)
    (by simp [Mutable.binary, scalarBinary, Nat.cast_add])

theorem days_before_year.heap_result (year : Int) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "days_before_year" [.scalar (.int year)] heap
      (.scalar (.int (ProjectEulerStatements.P19.daysBeforeYear year.toNat))) (heap ++ extra) := by
  let env := functionEnv [{name := "y", annotation := some (.name "int")}]
    ((findFunctionIn program.body "days_before_year").getD ([], [])).2 [.scalar (.int year)] []
  let summed := setLocal (comprehensionEnv env
    [("i", .call (.name "range") [.binOp (.name "y") .sub (.constant (.int 1900))], [])])
    sumAccumulator (.scalar (.int 0))
  by_cases afterEpoch : 1900 ≤ year
  · obtain ⟨extra, loop⟩ := calendarSum.loop yearElement
      (fun i => (ProjectEulerStatements.P19.daysInYear (1900 + i) : Int)) (fun _ => True)
      (by intros; trivial)
      (by intro heap env i _ lookup; exact ⟨[], by simpa using yearElement.result heap env i lookup⟩)
      (year - 1900).toNat 0 0 heap summed trivial (by simp [summed, setLocal])
    have total : ((List.range' 0 (year - 1900).toNat).map
        (fun i => (ProjectEulerStatements.P19.daysInYear (1900 + i) : Int))).sum =
        (ProjectEulerStatements.P19.daysBeforeYear year.toNat : Int) := by
      rw [← List.range_eq_range', ProjectEulerStatements.P19.daysBeforeYear_eq_sum]
      have count : (year - 1900).toNat = year.toNat - 1900 := by omega
      simp only [count, Nat.cast_list_sum, List.map_map, Function.comp_def]
    refine ⟨extra, ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.sum_range
    apply Evaluates.sum_generator_range
      (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil)
      rfl Evaluates.constant rfl
    simpa only [Nat.zero_add, Int.zero_add, total,
      show ((year - 1900).toNat : Int) = year - 1900 by omega] using loop
  · refine ⟨[], ?_⟩
    have empty : year.toNat - 1900 = 0 := by omega
    simp only [List.append_nil, ProjectEulerStatements.P19.daysBeforeYear, empty,
      List.range_zero, List.foldl_nil, Nat.cast_zero]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.sum_range
    apply Evaluates.sum_generator_range
      (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil)
      rfl Evaluates.constant rfl
    apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup (by simp [setLocal]))

private abbrev monthElement : Expr :=
  .call (.name "days_in_month") [.name "y", .binOp (.name "i") .add (.constant (.int 1))]

private theorem monthElement.result (year : Int) (heap : Mutable.Heap) (env : Mutable.Env) (i : Nat)
    (lookupYear : env "y" = some (.scalar (.int year)))
    (lookupIndex : env "i" = some (.scalar (.int i))) :
    ∃ extra, Evaluates program env monthElement heap
      (.scalar (.int (daysInMonthInt year ((i + 1 : Nat) : Int)))) (heap ++ extra) := by
  obtain ⟨extra, called⟩ := days_in_month.heap_result year ((i + 1 : Nat) : Int) heap
  refine ⟨extra, Evaluates.call ?_ called⟩
  apply Evaluates.Arguments.cons (Evaluates.lookup lookupYear)
  apply Evaluates.Arguments.cons _ .nil
  exact Evaluates.binary (Evaluates.lookup lookupIndex) Evaluates.constant
    (by simp [Mutable.binary, scalarBinary, Nat.cast_add])

theorem days_before_month.heap_result (year month : Int) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "days_before_month" [.scalar (.int year), .scalar (.int month)] heap
      (.scalar (.int (daysBeforeMonthInt year month))) (heap ++ extra) := by
  let env := functionEnv
    [{name := "y", annotation := some (.name "int")}, {name := "m", annotation := some (.name "int")}]
    ((findFunctionIn program.body "days_before_month").getD ([], [])).2
    [.scalar (.int year), .scalar (.int month)] []
  let summed := setLocal (comprehensionEnv env
    [("i", .call (.name "range") [.binOp (.name "m") .sub (.constant (.int 1))], [])])
    sumAccumulator (.scalar (.int 0))
  by_cases positive : 1 ≤ month
  · obtain ⟨extra, loop⟩ := calendarSum.loop monthElement
      (fun i => daysInMonthInt year ((i + 1 : Nat) : Int))
      (fun env => env "y" = some (.scalar (.int year)))
      (by intro env name value lookup assigned; rcases assigned with rfl | rfl <;>
          simpa [setLocal, sumAccumulator] using lookup)
      (monthElement.result year)
      (month - 1).toNat 0 0 heap summed rfl (by simp [summed, setLocal])
    refine ⟨extra, ?_⟩
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.sum_range
    apply Evaluates.sum_generator_range
      (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil)
      rfl Evaluates.constant rfl
    simpa only [Nat.zero_add, Int.zero_add, ← List.range_eq_range', daysBeforeMonthInt,
      show ((month - 1).toNat : Int) = month - 1 by omega] using loop
  · refine ⟨[], ?_⟩
    have empty : (month - 1).toNat = 0 := by omega
    simp only [List.append_nil, daysBeforeMonthInt, empty, List.range_zero, List.map_nil, List.sum_nil]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.return_value
    apply Evaluates.sum_range
    apply Evaluates.sum_generator_range
      (.cons (Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl) .nil)
      rfl Evaluates.constant rfl
    apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup (by simp [setLocal]))

open ProjectEulerStatements.P19 (dateOrdinalInt dayOfWeekInt)

theorem day_of_week.heap_result (year month day : Int) (heap : Mutable.Heap) :
    ∃ extra, ReturnsValue program "day_of_week" [.scalar (.int year), .scalar (.int month), .scalar (.int day)]
      heap (.scalar (.int (dayOfWeekInt year month day))) (heap ++ extra) := by
  obtain ⟨yearExtra, years⟩ := days_before_year.heap_result year heap
  obtain ⟨monthExtra, months⟩ := days_before_month.heap_result year month (heap ++ yearExtra)
  refine ⟨yearExtra ++ monthExtra, ?_⟩
  rw [← List.append_assoc]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  refine Evaluates.binary (av := .scalar (.int (dateOrdinalInt year month day)))
    (bv := .scalar (.int 7)) (middle := heap ++ yearExtra ++ monthExtra) ?_ Evaluates.constant ?_
  · apply Evaluates.binary
      (av := .scalar (.int ((ProjectEulerStatements.P19.daysBeforeYear year.toNat : Int) + daysBeforeMonthInt year month)))
      (bv := .scalar (.int (day - 1)))
    · apply Evaluates.binary
        (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) years)
        (Evaluates.call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) months)
      rfl
    · exact Evaluates.binary (Evaluates.lookup rfl) Evaluates.constant rfl
    · rfl
  · simp [Mutable.binary, scalarBinary, dayOfWeekInt]

private abbrev dateOrigin := (program.classOrigins.lookup "Date").getD ""
private abbrev TypedDate (heap : Mutable.Heap) (address : Nat) :=
  Mutable.Value.HasRecordType heap (.ref address) dateOrigin "Date" true
    [("year", "int"), ("month", "int"), ("day", "int")]

private def DateFields (heap : Mutable.Heap) (address : Nat) (year month day : Int) : Prop :=
  ∃ fields, heap[address]? = some (.dataInstance dateOrigin "Date" true ["year", "month", "day"] fields) ∧
    fields.lookup "year" = some (.scalar (.int year)) ∧
    fields.lookup "month" = some (.scalar (.int month)) ∧ fields.lookup "day" = some (.scalar (.int day))

private theorem integer_value (heap : Mutable.Heap) (value : Mutable.Value)
    (typed : Mutable.Value.HasType heap value "int") : ∃ n : Int, value = .scalar (.int n) := by
  cases value with
  | scalar value => cases value <;> simp_all [Mutable.Value.HasType]
  | ref address =>
      change ∃ items, heap[address]? = some (.list items) ∧
        ("int" = "list" ∨ ∃ kind, ∃ (_ : "int" = "list[" ++ kind ++ "]"), _) at typed
      obtain ⟨items, found, domain⟩ := typed
      rcases domain with impossible | ⟨kind, same, _⟩
      · simp at impossible
      · have size := congrArg String.length same
        rw [String.length_append, String.length_append] at size
        change 3 = 5 + kind.length + 1 at size
        omega

private theorem DateFields.of_typed (heap : Mutable.Heap) (address : Nat) (typed : TypedDate heap address) :
    ∃ year month day, DateFields heap address year month day := by
  obtain ⟨fields, found, types⟩ := typed
  obtain ⟨yearValue, getYear, yearType⟩ := types ("year", "int") (by simp)
  obtain ⟨monthValue, getMonth, monthType⟩ := types ("month", "int") (by simp)
  obtain ⟨dayValue, getDay, dayType⟩ := types ("day", "int") (by simp)
  obtain ⟨year, rfl⟩ := integer_value heap yearValue yearType
  obtain ⟨month, rfl⟩ := integer_value heap monthValue monthType
  obtain ⟨day, rfl⟩ := integer_value heap dayValue dayType
  exact ⟨year, month, day, fields, found, getYear, getMonth, getDay⟩

private theorem DateFields.append (h : DateFields heap address year month day) (extra : Mutable.Heap) :
    DateFields (heap ++ extra) address year month day := by
  obtain ⟨fields, found, rest⟩ := h
  refine ⟨fields, ?_, rest⟩
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

private theorem DateFields.read (h : DateFields heap address year month day) (env : Mutable.Env)
    (name field : String) (value : Int) (lookup : env name = some (.ref address))
    (selected : (field, value) ∈ [("year", year), ("month", month), ("day", day)]) :
    Evaluates program env (.attribute (.name name) field) heap (.scalar (.int value)) heap := by
  obtain ⟨fields, found, getYear, getMonth, getDay⟩ := h
  apply Evaluates.field (Evaluates.lookup lookup)
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at selected
  rcases selected with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [getAttribute, instanceClass, found, getYear, getMonth, getDay, program, P19Ast.module,
      Module.findClass, Module.findClassBody, findClassBodyIn, dateOrigin]

theorem date_to_days.heap_result (heap : Mutable.Heap) (address : Nat) (year month day : Int)
    (fields : DateFields heap address year month day) :
    ∃ extra, ReturnsValue program "date_to_days" [.ref address] heap
      (.scalar (.int (dateOrdinalInt year month day))) (heap ++ extra) := by
  let env := functionEnv [{name := "d", annotation := some (.name "Date")}]
    ((findFunctionIn program.body "date_to_days").getD ([], [])).2 [.ref address] []
  obtain ⟨yearExtra, years⟩ := days_before_year.heap_result year heap
  obtain ⟨monthExtra, months⟩ := days_before_month.heap_result year month (heap ++ yearExtra)
  have yearRead := fields.read env "d" "year" year rfl (by simp)
  have laterYear := (fields.append yearExtra).read env "d" "year" year rfl (by simp)
  have monthRead := (fields.append yearExtra).read env "d" "month" month rfl (by simp)
  have dayRead := ((fields.append yearExtra).append monthExtra).read env "d" "day" day rfl (by simp)
  refine ⟨yearExtra ++ monthExtra, ?_⟩
  rw [← List.append_assoc]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.binary
    (av := .scalar (.int ((ProjectEulerStatements.P19.daysBeforeYear year.toNat : Int) + daysBeforeMonthInt year month)))
    (bv := .scalar (.int (day - 1)))
  · apply Evaluates.binary (Evaluates.call (.cons yearRead .nil) years)
      (Evaluates.call (.cons laterYear (.cons monthRead .nil)) months)
    rfl
  · exact Evaluates.binary dayRead Evaluates.constant rfl
  · rfl

theorem date_to_days.«Returns» (heap : Mutable.Heap) (address : Nat) (_valid : heap.Valid)
    (typed : TypedDate heap address) : (HeapCalls.call program "date_to_days" [.ref address] heap).Returns := by
  obtain ⟨year, month, day, fields⟩ := DateFields.of_typed heap address typed
  obtain ⟨extra, returned⟩ := date_to_days.heap_result heap address year month day fields
  exact returned.returns

theorem date_to_days.«Supported» (heap : Mutable.Heap) (address : Nat) (valid : heap.Valid)
    (typed : TypedDate heap address) : (HeapCalls.call program "date_to_days" [.ref address] heap).Supported :=
  (date_to_days.«Returns» heap address valid typed).supported

open ProjectEulerStatements.P19 (intervalSunday intervalMonths intervalYears)

private abbrev offsetExpr : Expr := .binOp
  (.call (.name "days_before_year") [.name "y"]) .add
  (.call (.name "days_before_month") [.name "y", .name "m"])

private theorem offsetExpr.result (year month : Int) (heap : Mutable.Heap) (env : Mutable.Env)
    (getYear : env "y" = some (.scalar (.int year))) (getMonth : env "m" = some (.scalar (.int month))) :
    ∃ extra, Evaluates program env offsetExpr heap (.scalar (.int (dateOrdinalInt year month 1))) (heap ++ extra) := by
  obtain ⟨yearExtra, years⟩ := days_before_year.heap_result year heap
  obtain ⟨monthExtra, months⟩ := days_before_month.heap_result year month (heap ++ yearExtra)
  refine ⟨yearExtra ++ monthExtra, ?_⟩
  rw [← List.append_assoc]
  apply Evaluates.binary (Evaluates.call (.cons (Evaluates.lookup getYear) .nil) years)
    (Evaluates.call (.cons (Evaluates.lookup getYear) (.cons (Evaluates.lookup getMonth) .nil)) months)
  simp only [dateOrdinalInt, Int.sub_self, Int.add_zero]
  rfl

private abbrev withinExpr : Expr :=
  .compare (.name "start_days") [(.ltE, .name "days"), (.ltE, .name "end_days")]

private theorem withinExpr.result (first last days : Int) (heap : Mutable.Heap) (env : Mutable.Env)
    (getFirst : env "start_days" = some (.scalar (.int first)))
    (getLast : env "end_days" = some (.scalar (.int last)))
    (getDays : env "days" = some (.scalar (.int days))) :
    Evaluates program env withinExpr heap (.scalar (.bool (decide (first ≤ days ∧ days ≤ last)))) heap := by
  by_cases lower : first ≤ days
  · apply Evaluates.chain (Evaluates.lookup getFirst)
    apply Evaluates.Compares.next (value := .scalar (.int days)) (compared := .scalar (.bool true))
      (afterComparison := heap) (Evaluates.lookup getDays)
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
    · rfl
    · apply Evaluates.Compares.last (middle := heap) (Evaluates.lookup getLast)
      simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
  · simp only [lower, false_and, decide_false]
    apply Evaluates.chain (Evaluates.lookup getFirst)
    apply Evaluates.Compares.stop (middle := heap) (Evaluates.lookup getDays)
    · simp [HeapCalls.compare, scalarCompare, evalCmpOp, lower]
    · rfl

private abbrev countTest : Expr := .boolOp .and
  [withinExpr, .compare (.call (.name "day_of_week") [.name "y", .name "m", .constant (.int 1)])
    [(.eq, .constant (.int 6))]]

private theorem countTest.result (first last year month : Int) (heap : Mutable.Heap) (env : Mutable.Env)
    (getFirst : env "start_days" = some (.scalar (.int first)))
    (getLast : env "end_days" = some (.scalar (.int last)))
    (getYear : env "y" = some (.scalar (.int year))) (getMonth : env "m" = some (.scalar (.int month)))
    (getDays : env "days" = some (.scalar (.int (dateOrdinalInt year month 1)))) :
    ∃ extra, Evaluates program env countTest heap (.scalar (.bool (intervalSunday first last year month)))
      (heap ++ extra) := by
  have within := withinExpr.result first last (dateOrdinalInt year month 1) heap env getFirst getLast getDays
  by_cases inside : first ≤ dateOrdinalInt year month 1 ∧ dateOrdinalInt year month 1 ≤ last
  · obtain ⟨extra, weekday⟩ := day_of_week.heap_result year month 1 heap
    refine ⟨extra, ?_⟩
    have test : Evaluates program env withinExpr heap (.scalar (.bool true)) heap := by simpa [inside] using within
    have selected : intervalSunday first last year month = decide (dayOfWeekInt year month 1 = 6) := by
      simp [intervalSunday, inside.1, inside.2]
    rw [selected]
    apply Evaluates.boolean_next (middle := heap) test rfl rfl
    apply Evaluates.boolean_last (flag := decide (dayOfWeekInt year month 1 = 6))
    · apply Evaluates.compare (afterRight := heap ++ extra)
        (Evaluates.call (.cons (Evaluates.lookup getYear) (.cons (Evaluates.lookup getMonth) (.cons .constant .nil))) weekday)
        Evaluates.constant
      simp [HeapCalls.compare, scalarCompare, evalCmpOp]
    · rfl
  · refine ⟨[], ?_⟩
    have selected : intervalSunday first last year month = false := by
      simp only [intervalSunday, decide_eq_false_iff_not]
      tauto
    rw [List.append_nil, selected]
    apply Evaluates.boolean_stop (value := .scalar (.bool false))
    · simpa [inside] using within
    · rfl
    · rfl

private abbrev monthBody : List Stmt :=
  [.assign [.name "days"] offsetExpr,
    .ifThen countTest [.augAssign (.name "acc") .add (.constant (.int 1))] []]

private def CountEnv (env : Mutable.Env) (first last count : Int) : Prop :=
  env "start_days" = some (.scalar (.int first)) ∧ env "end_days" = some (.scalar (.int last)) ∧
    env "acc" = some (.scalar (.int count))

private theorem CountEnv.set_other (h : CountEnv env first last count) (name : String) (value : Mutable.Value)
    (ordinary : name ≠ "start_days" ∧ name ≠ "end_days" ∧ name ≠ "acc") :
    CountEnv (setLocal env name value) first last count := by
  simpa [CountEnv, setLocal, Ne.symm ordinary.1, Ne.symm ordinary.2.1, Ne.symm ordinary.2.2] using h

private theorem CountEnv.set_acc (h : CountEnv env first last count) (next : Int) :
    CountEnv (setLocal env "acc" (.scalar (.int next))) first last next := by
  simpa [CountEnv, setLocal] using And.intro h.1 h.2.1

private theorem monthBody.result (first last year month count : Int) (heap : Mutable.Heap) (env : Mutable.Env)
    (saved : CountEnv env first last count) (getYear : env "y" = some (.scalar (.int year)))
    (getMonth : env "m" = some (.scalar (.int month))) :
    ∃ extra finalEnv, BlockContinues program env monthBody heap finalEnv (heap ++ extra) ∧
      CountEnv finalEnv first last (count + if intervalSunday first last year month then 1 else 0) ∧
      finalEnv "y" = some (.scalar (.int year)) := by
  obtain ⟨offsetExtra, offset⟩ := offsetExpr.result year month heap env getYear getMonth
  let withDays := setLocal env "days" (.scalar (.int (dateOrdinalInt year month 1)))
  have savedDays : CountEnv withDays first last count := saved.set_other "days" _ (by decide)
  have yearDays : withDays "y" = some (.scalar (.int year)) := by simpa [withDays, setLocal] using getYear
  have monthDays : withDays "m" = some (.scalar (.int month)) := by simpa [withDays, setLocal] using getMonth
  obtain ⟨testExtra, test⟩ := countTest.result first last year month (heap ++ offsetExtra) withDays
    savedDays.1 savedDays.2.1 yearDays monthDays (by simp [withDays, setLocal])
  have assigned : BlockContinues program env [.assign [.name "days"] offsetExpr] heap withDays
      (heap ++ offsetExtra) := BlockContinues.assign offset
  cases selected : intervalSunday first last year month with
  | false =>
      refine ⟨offsetExtra ++ testExtra, withDays, ?_, ?_, yearDays⟩
      · rw [← List.append_assoc]
        apply assigned.append
        apply BlockContinues.branch (flag := false)
        · simpa only [selected] using test
        · rfl
        · exact BlockContinues.nil
      · simpa only [selected, Bool.false_eq_true, ↓reduceIte, Int.add_zero] using savedDays
  | true =>
      let finalEnv := setLocal withDays "acc" (.scalar (.int (count + 1)))
      refine ⟨offsetExtra ++ testExtra, finalEnv, ?_, ?_, ?_⟩
      · rw [← List.append_assoc]
        apply assigned.append
        apply BlockContinues.branch (flag := true)
        · simpa only [selected] using test
        · rfl
        · exact BlockContinues.augAssign savedDays.2.2 Evaluates.constant rfl
      · simpa only [selected, ↓reduceIte] using savedDays.set_acc (count + 1)
      · simpa [finalEnv, setLocal] using yearDays

private theorem monthLoop.result (first last year : Int) (month count : Nat) (initial : Int)
    (heap : Mutable.Heap) (env : Mutable.Env) (saved : CountEnv env first last initial)
    (getYear : env "y" = some (.scalar (.int year))) :
    ∃ extra finalEnv, BlockContinues program env
      [.rangeStepLoop "m" (month : Int) ((month + count : Nat) : Int) 1 monthBody []]
      heap finalEnv (heap ++ extra) ∧
      CountEnv finalEnv first last (initial + intervalMonths first last year month count) ∧
      finalEnv "y" = some (.scalar (.int year)) := by
  induction count generalizing month initial heap env with
  | zero =>
      refine ⟨[], env, ?_, ?_, getYear⟩
      · simp only [List.append_nil, Nat.add_zero]
        exact BlockContinues.range_done (by simp [Calls.rangeContinues]) BlockContinues.nil
      · simpa only [ProjectEulerStatements.P19.intervalMonths_zero, Int.add_zero] using saved
  | succ count ih =>
      let withMonth := setLocal env "m" (.scalar (.int month))
      have savedMonth : CountEnv withMonth first last initial := saved.set_other "m" _ (by decide)
      have yearMonth : withMonth "y" = some (.scalar (.int year)) := by simpa [withMonth, setLocal] using getYear
      obtain ⟨allocated, middleEnv, body, savedBody, yearBody⟩ :=
        monthBody.result first last year month initial heap withMonth savedMonth yearMonth (by simp [withMonth, setLocal])
      obtain ⟨later, finalEnv, continued, savedFinal, yearFinal⟩ :=
        ih (month + 1) _ (heap ++ allocated) middleEnv savedBody yearBody
      refine ⟨allocated ++ later, finalEnv, ?_, ?_, yearFinal⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues])
        change BlockContinues program withMonth
          (monthBody ++ [.rangeStepLoop "m" ((month : Int) + 1) ((month + (count + 1) : Nat) : Int) 1 monthBody []])
          heap finalEnv (heap ++ (allocated ++ later))
        simpa only [Nat.cast_add, Nat.cast_one, Int.add_assoc, Int.add_left_comm, Int.add_comm,
          List.append_assoc] using body.append continued
      · simpa only [ProjectEulerStatements.P19.intervalMonths_succ, Int.add_assoc] using savedFinal

private abbrev yearBody : List Stmt :=
  [.forIn (.name "m") (.call (.name "range") [.constant (.int 1), .constant (.int 13)]) monthBody []]

private theorem yearBody.result (first last year initial : Int) (heap : Mutable.Heap) (env : Mutable.Env)
    (saved : CountEnv env first last initial) (getYear : env "y" = some (.scalar (.int year))) :
    ∃ extra finalEnv, BlockContinues program env yearBody heap finalEnv (heap ++ extra) ∧
      CountEnv finalEnv first last (initial + intervalMonths first last year 1 12) := by
  obtain ⟨extra, finalEnv, loop, savedFinal, _⟩ := monthLoop.result first last year 1 12 initial heap env saved getYear
  refine ⟨extra, finalEnv, ?_, savedFinal⟩
  exact BlockContinues.for_range (.cons .constant (.cons .constant .nil)) rfl loop

private theorem yearLoop.result (first last year : Int) (count : Nat) (initial : Int)
    (heap : Mutable.Heap) (env : Mutable.Env) (saved : CountEnv env first last initial) :
    ∃ extra finalEnv, BlockContinues program env
      [.rangeStepLoop "y" year (year + count) 1 yearBody []] heap finalEnv (heap ++ extra) ∧
      CountEnv finalEnv first last (initial + intervalYears first last year count) := by
  induction count generalizing year initial heap env with
  | zero =>
      refine ⟨[], env, ?_, ?_⟩
      · simp only [List.append_nil, Nat.cast_zero, Int.add_zero]
        exact BlockContinues.range_done (by simp [Calls.rangeContinues]) BlockContinues.nil
      · simpa only [ProjectEulerStatements.P19.intervalYears_zero, Int.add_zero] using saved
  | succ count ih =>
      let withYear := setLocal env "y" (.scalar (.int year))
      have savedYear : CountEnv withYear first last initial := saved.set_other "y" _ (by decide)
      obtain ⟨allocated, middleEnv, body, savedBody⟩ :=
        yearBody.result first last year initial heap withYear savedYear (by simp [withYear, setLocal])
      obtain ⟨later, finalEnv, continued, savedFinal⟩ := ih (year + 1) _ (heap ++ allocated) middleEnv savedBody
      refine ⟨allocated ++ later, finalEnv, ?_, ?_⟩
      · apply BlockContinues.range_step (by simp [Calls.rangeContinues])
        change BlockContinues program withYear
          (yearBody ++ [.rangeStepLoop "y" (year + 1) (year + (count + 1 : Nat)) 1 yearBody []])
          heap finalEnv (heap ++ (allocated ++ later))
        simpa only [Nat.cast_add, Nat.cast_one, Int.add_assoc, Int.add_left_comm, Int.add_comm,
          List.append_assoc] using body.append continued
      · simpa only [ProjectEulerStatements.P19.intervalYears_succ, Int.add_assoc] using savedFinal

open ProjectEulerStatements.P19 (countSundaysInt)

theorem count_sundays_between.heap_result (heap : Mutable.Heap) (startAddress endAddress : Nat)
    (sy sm sd ey em ed : Int) (startFields : DateFields heap startAddress sy sm sd)
    (endFields : DateFields heap endAddress ey em ed) :
    ∃ extra, ReturnsValue program "count_sundays_between" [.ref startAddress, .ref endAddress] heap
      (.scalar (.int (countSundaysInt sy sm sd ey em ed))) (heap ++ extra) := by
  let first := dateOrdinalInt sy sm sd
  let last := dateOrdinalInt ey em ed
  let env := functionEnv
    [{name := "start_date", annotation := some (.name "Date")}, {name := "end_date", annotation := some (.name "Date")}]
    ((findFunctionIn program.body "count_sundays_between").getD ([], [])).2 [.ref startAddress, .ref endAddress] []
  obtain ⟨startExtra, startResult⟩ := date_to_days.heap_result heap startAddress sy sm sd startFields
  obtain ⟨endExtra, endResult⟩ := date_to_days.heap_result (heap ++ startExtra) endAddress ey em ed (endFields.append startExtra)
  let initialEnv := setLocal (setLocal (setLocal env "start_days" (.scalar (.int first)))
    "end_days" (.scalar (.int last))) "acc" (.scalar (.int 0))
  have saved : CountEnv initialEnv first last 0 := by constructor <;> first | rfl | constructor <;> rfl
  have startYear := ((startFields.append startExtra).append endExtra).read initialEnv "start_date" "year" sy rfl (by simp)
  have endYear := ((endFields.append startExtra).append endExtra).read initialEnv "end_date" "year" ey rfl (by simp)
  by_cases ordered : sy ≤ ey + 1
  · obtain ⟨loopExtra, finalEnv, loop, savedFinal⟩ :=
      yearLoop.result first last sy (ey + 1 - sy).toNat 0 (heap ++ startExtra ++ endExtra) initialEnv saved
    refine ⟨startExtra ++ endExtra ++ loopExtra, ?_⟩
    simp only [← List.append_assoc]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) startResult)
    apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) endResult)
    apply BlockReturns.assign Evaluates.constant
    apply BlockReturns.for_range (.cons startYear (.cons (Evaluates.binary endYear Evaluates.constant rfl) .nil)) rfl
    have actualLoop : BlockContinues program initialEnv [.rangeStepLoop "y" sy (ey + 1) 1 yearBody []]
        (heap ++ startExtra ++ endExtra) finalEnv ((heap ++ startExtra ++ endExtra) ++ loopExtra) := by
      simpa only [show sy + ((ey + 1 - sy).toNat : Int) = ey + 1 by omega] using loop
    apply actualLoop.returns
    apply BlockReturns.return_value
    exact Evaluates.lookup (by simpa only [Int.zero_add] using savedFinal.2.2)
  · refine ⟨startExtra ++ endExtra, ?_⟩
    have empty : (ey + 1 - sy).toNat = 0 := by omega
    simp only [countSundaysInt, empty, ProjectEulerStatements.P19.intervalYears_zero, ← List.append_assoc]
    apply BlockReturns.function rfl rfl
    apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) startResult)
    apply BlockReturns.assign (Evaluates.call (.cons (Evaluates.lookup rfl) .nil) endResult)
    apply BlockReturns.assign Evaluates.constant
    apply BlockReturns.for_range (.cons startYear (.cons (Evaluates.binary endYear Evaluates.constant rfl) .nil)) rfl
    apply BlockReturns.range_done (by simp [Calls.rangeContinues]; omega)
    exact BlockReturns.return_value (Evaluates.lookup rfl)

theorem naive.heap_result (heap : Mutable.Heap) (startAddress endAddress : Nat)
    (sy sm sd ey em ed : Int) (startFields : DateFields heap startAddress sy sm sd)
    (endFields : DateFields heap endAddress ey em ed) :
    ∃ extra, ReturnsValue program "naive" [.ref startAddress, .ref endAddress] heap
      (.scalar (.int (countSundaysInt sy sm sd ey em ed))) (heap ++ extra) := by
  obtain ⟨extra, counted⟩ := count_sundays_between.heap_result heap startAddress endAddress sy sm sd ey em ed startFields endFields
  refine ⟨extra, ?_⟩
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  exact Evaluates.call (.cons (Evaluates.lookup rfl) (.cons (Evaluates.lookup rfl) .nil)) counted

theorem naive.«Returns» (heap : Mutable.Heap) (startAddress endAddress : Nat) (_valid : heap.Valid)
    (startTyped : TypedDate heap startAddress) (endTyped : TypedDate heap endAddress) :
    (HeapCalls.call program "naive" [.ref startAddress, .ref endAddress] heap).Returns := by
  obtain ⟨sy, sm, sd, startFields⟩ := DateFields.of_typed heap startAddress startTyped
  obtain ⟨ey, em, ed, endFields⟩ := DateFields.of_typed heap endAddress endTyped
  obtain ⟨extra, counted⟩ := naive.heap_result heap startAddress endAddress sy sm sd ey em ed startFields endFields
  exact counted.returns

theorem naive.«Supported» (heap : Mutable.Heap) (startAddress endAddress : Nat) (valid : heap.Valid)
    (startTyped : TypedDate heap startAddress) (endTyped : TypedDate heap endAddress) :
    (HeapCalls.call program "naive" [.ref startAddress, .ref endAddress] heap).Supported :=
  (naive.«Returns» heap startAddress endAddress valid startTyped endTyped).supported

private abbrev dateObject (year month day : Int) : Mutable.Object :=
  .dataInstance dateOrigin "Date" true ["year", "month", "day"]
    [("year", .scalar (.int year)), ("month", .scalar (.int month)), ("day", .scalar (.int day))]

private theorem dateObject.fields (heap : Mutable.Heap) (year month day : Int) :
    DateFields (heap ++ [dateObject year month day]) heap.length year month day := by
  refine ⟨[("year", .scalar (.int year)), ("month", .scalar (.int month)), ("day", .scalar (.int day))], ?_⟩
  simp [dateObject, List.lookup]

private theorem Date.constructor (heap : Mutable.Heap) (year month day : Int) :
    ReturnsValue program "Date" [.scalar (.int year), .scalar (.int month), .scalar (.int day)] heap
      (.ref heap.length) (heap ++ [dateObject year month day]) := by
  exact ReturnsValue.dataclass_constructor
    (fields := [{name := "year", annotation := some (.name "int")},
      {name := "month", annotation := some (.name "int")}, {name := "day", annotation := some (.name "int")}])
    rfl rfl rfl rfl rfl rfl

theorem naive_years.heap_result (heap : Mutable.Heap) (startYear endYear : Int) :
    ∃ extra, ReturnsValue program "naive_years" [.scalar (.int startYear), .scalar (.int endYear)] heap
      (.scalar (.int (countSundaysInt startYear 1 1 endYear 12 31))) (heap ++ extra) := by
  let startHeap := heap ++ [dateObject startYear 1 1]
  let endHeap := startHeap ++ [dateObject endYear 12 31]
  have startFields := (dateObject.fields heap startYear 1 1).append [dateObject endYear 12 31]
  have endFields := dateObject.fields startHeap endYear 12 31
  obtain ⟨extra, counted⟩ := naive.heap_result endHeap heap.length startHeap.length startYear 1 1 endYear 12 31 startFields endFields
  refine ⟨[dateObject startYear 1 1, dateObject endYear 12 31] ++ extra, ?_⟩
  have allocated : heap ++ ([dateObject startYear 1 1, dateObject endYear 12 31] ++ extra) = endHeap ++ extra := by
    simp [endHeap, startHeap, List.append_assoc]
  rw [allocated]
  apply BlockReturns.function rfl rfl
  apply BlockReturns.return_value
  apply Evaluates.call _ counted
  apply Evaluates.Arguments.cons
    (Evaluates.call (.cons (Evaluates.lookup rfl) (.cons .constant (.cons .constant .nil)))
      (Date.constructor heap startYear 1 1))
  exact .cons (Evaluates.call (.cons (Evaluates.lookup rfl) (.cons .constant (.cons .constant .nil)))
    (Date.constructor startHeap endYear 12 31)) .nil

theorem naive_years.«Returns» (startYear endYear : Int) :
    (HeapCalls.scalarFunction program "naive_years" [.int startYear, .int endYear]).Returns := by
  obtain ⟨extra, counted⟩ := naive_years.heap_result [] startYear endYear
  exact counted.scalar_returns

theorem naive_years.«Supported» (startYear endYear : Int) :
    (HeapCalls.scalarFunction program "naive_years" [.int startYear, .int endYear]).Supported :=
  (naive_years.«Returns» startYear endYear).supported

/-- The whole-year adapter computes the reusable calendar count on its comparison domain. -/
theorem naive_years.result (heap : Mutable.Heap) (startYear endYear : Nat)
    (afterEpoch : 1900 ≤ startYear) (ordered : startYear ≤ endYear) :
    ∃ extra, ReturnsValue program "naive_years" [.scalar (.int startYear), .scalar (.int endYear)] heap
      (.scalar (.int (ProjectEulerStatements.P19.sundaysInYears startYear (endYear + 1 - startYear))))
      (heap ++ extra) := by
  obtain ⟨extra, returned⟩ := naive_years.heap_result heap startYear endYear
  refine ⟨extra, ?_⟩
  simpa only [ProjectEulerStatements.P19.countSundaysInt_whole_years startYear endYear afterEpoch ordered] using returned

end data.«project-euler-statements».data.py.project_euler_statements.p19
