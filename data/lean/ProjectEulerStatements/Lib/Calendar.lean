import ProjectEulerStatements.P19

/-! Calendar sums and weekday transitions, with Monday 1 January 1900 as day zero. -/
namespace ProjectEulerStatements.P19

/-- The leap-year test on Python's signed integer year domain. -/
def isLeapInt (year : Int) : Bool :=
  (year % 4 = 0) && ((year % 100 ≠ 0) || (year % 400 = 0))

@[simp] theorem isLeapInt_nat (year : Nat) : isLeapInt year = isLeap year := by
  unfold isLeapInt isLeap
  norm_cast

theorem isLeapInt_eq_century_test (year : Int) :
    isLeapInt year = (if year % 400 = 0 then true
      else if year % 100 = 0 then false else decide (year % 4 = 0)) := by
  by_cases century : year % 400 = 0
  · have fourth : year % 4 = 0 := by omega
    simp [isLeapInt, century, fourth]
  · by_cases hundred : year % 100 = 0 <;> simp [isLeapInt, century, hundred]


/-- Calendar helpers on Python's unrestricted signed year and month arguments. -/
def daysInYearInt (year : Int) : Int := if isLeapInt year then 366 else 365

def daysInMonthInt (year month : Int) : Int :=
  match month.toNat with
  | 1 => 31
  | 2 => if isLeapInt year then 29 else 28
  | 3 => 31
  | 4 => 30
  | 5 => 31
  | 6 => 30
  | 7 => 31
  | 8 => 31
  | 9 => 30
  | 10 => 31
  | 11 => 30
  | 12 => 31
  | _ => 0

def daysBeforeMonthInt (year month : Int) : Int :=
  ((List.range (month - 1).toNat).map (fun i => daysInMonthInt year ((i + 1 : Nat) : Int))).sum

theorem daysInMonthInt_outside (year month : Int) (outside : month < 1 ∨ 12 < month) :
    daysInMonthInt year month = 0 := by
  unfold daysInMonthInt
  split <;> omega

@[simp] theorem daysInYearInt_nat (year : Nat) : daysInYearInt year = (daysInYear year : Int) := by
  simp only [daysInYearInt, daysInYear, isLeapInt_nat]
  split <;> rfl

@[simp] theorem daysInMonthInt_nat (year month : Nat) :
    daysInMonthInt year month = (daysInMonth year month : Int) := by
  simp only [daysInMonthInt, Int.toNat_natCast, daysInMonth, isLeapInt_nat]
  split <;> first | rfl | simp

@[simp] theorem daysBeforeMonthInt_nat (year month : Nat) :
    daysBeforeMonthInt year month = (daysBeforeMonth year month : Int) := by
  have count : ((month : Int) - 1).toNat = month - 1 := by omega
  simp only [daysBeforeMonthInt, count]
  simp_rw [daysInMonthInt_nat]
  have total : ((List.range (month - 1)).map (fun i => daysInMonth year (i + 1))).sum =
      daysBeforeMonth year month := by
    simp [daysBeforeMonth, List.sum_eq_foldl, List.foldl_map]
  simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def] using
    congrArg (fun n : Nat => (n : Int)) total

/-- Signed offsets retain the Python helpers' behavior even for non-calendar inputs. -/
def dateOrdinalInt (year month day : Int) : Int :=
  (daysBeforeYear year.toNat : Int) + daysBeforeMonthInt year month + (day - 1)

def dayOfWeekInt (year month day : Int) : Int := dateOrdinalInt year month day % 7

/-- First-of-month Sundays selected by an inclusive interval of signed offsets. -/
def intervalSunday (firstDay lastDay year month : Int) : Bool :=
  decide (firstDay ≤ dateOrdinalInt year month 1 ∧ dateOrdinalInt year month 1 ≤ lastDay ∧
    dayOfWeekInt year month 1 = 6)

def intervalMonths (firstDay lastDay year : Int) (first count : Nat) : Int :=
  ((List.range count).map (fun i : Nat =>
    if intervalSunday firstDay lastDay year ((first + i : Nat) : Int) then 1 else 0)).sum

def intervalYears (firstDay lastDay first : Int) (count : Nat) : Int :=
  ((List.range count).map (fun i : Nat => intervalMonths firstDay lastDay (first + i) 1 12)).sum

def countSundaysInt (startYear startMonth startDay endYear endMonth endDay : Int) : Int :=
  intervalYears (dateOrdinalInt startYear startMonth startDay) (dateOrdinalInt endYear endMonth endDay)
    startYear (endYear + 1 - startYear).toNat

@[simp] theorem intervalMonths_zero (firstDay lastDay year : Int) (first : Nat) :
    intervalMonths firstDay lastDay year first 0 = 0 := rfl

@[simp] theorem intervalYears_zero (firstDay lastDay first : Int) :
    intervalYears firstDay lastDay first 0 = 0 := rfl

theorem intervalMonths_succ (firstDay lastDay year : Int) (first count : Nat) :
    intervalMonths firstDay lastDay year first (count + 1) =
      (if intervalSunday firstDay lastDay year first then 1 else 0) +
        intervalMonths firstDay lastDay year (first + 1) count := by
  unfold intervalMonths
  rw [show count + 1 = 1 + count by omega, List.range_add]
  simp [List.range_succ, List.map_map, Function.comp_def, Nat.add_assoc]

theorem intervalYears_succ (firstDay lastDay first : Int) (count : Nat) :
    intervalYears firstDay lastDay first (count + 1) = intervalMonths firstDay lastDay first 1 12 +
      intervalYears firstDay lastDay (first + 1) count := by
  unfold intervalYears
  rw [show count + 1 = 1 + count by omega, List.range_add]
  simp [List.range_succ, List.map_map, Function.comp_def, Int.add_assoc]

theorem dateOrdinalInt_nat (year month day : Nat) (positive : 1 ≤ day) :
    dateOrdinalInt year month day =
      ((daysBeforeYear year + daysBeforeMonth year month + (day - 1) : Nat) : Int) := by
  simp only [dateOrdinalInt, Int.toNat_natCast, daysBeforeMonthInt_nat, Nat.cast_add,
    Nat.cast_sub positive, Nat.cast_one]

theorem dateOrdinalInt_date (date : Date) :
    dateOrdinalInt date.year date.month date.day = (dateToDays date : Int) :=
  dateOrdinalInt_nat date.year date.month date.day date.day_pos

theorem dayOfWeekInt_nat (year month day : Nat) (positive : 1 ≤ day) :
    dayOfWeekInt year month day = (dayOfWeek year month day : Int) := by
  rw [dayOfWeekInt, dateOrdinalInt_nat year month day positive]
  exact (Int.natCast_emod _ 7).symm

private theorem foldl_add_map (xs : List α) (f : α → Nat) (initial : Nat) :
    xs.foldl (fun acc x => acc + f x) initial = initial + (xs.map f).sum := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

theorem daysBeforeYear_eq_sum (year : Nat) :
    daysBeforeYear year = ((List.range (year - 1900)).map
      (fun i => daysInYear (1900 + i))).sum := by
  simp [daysBeforeYear, foldl_add_map]

theorem daysBeforeMonth_eq_sum (year month : Nat) :
    daysBeforeMonth year month = ((List.range (month - 1)).map
      (fun i => daysInMonth year (i + 1))).sum := by
  simp [daysBeforeMonth, foldl_add_map]

theorem isLeap_eq_century_test (year : Nat) :
    isLeap year = (if year % 400 == 0 then true
      else if year % 100 == 0 then false else year % 4 == 0) := by
  by_cases century : year % 400 = 0
  · have fourth : year % 4 = 0 := by omega
    simp [isLeap, century, fourth]
  · by_cases hundred : year % 100 = 0
    · simp [isLeap, century, hundred]
    · simp [isLeap, century, hundred]
      rfl

theorem daysInMonth_bounds (year month : Nat) (positive : 0 < month) (bound : month ≤ 12) :
    28 ≤ daysInMonth year month ∧ daysInMonth year month ≤ 31 := by
  interval_cases month <;> simp [daysInMonth]
  split <;> omega

@[simp] theorem daysBeforeMonth_one (year : Nat) : daysBeforeMonth year 1 = 0 := rfl

@[simp] theorem daysBeforeYear_epoch : daysBeforeYear 1900 = 0 := rfl

theorem daysBeforeYear_succ (year : Nat) (afterEpoch : 1900 ≤ year) :
    daysBeforeYear (year + 1) = daysBeforeYear year + daysInYear year := by
  rw [daysBeforeYear_eq_sum, daysBeforeYear_eq_sum,
    show year + 1 - 1900 = (year - 1900) + 1 by omega, List.range_succ]
  simp [show 1900 + (year - 1900) = year by omega]

theorem daysBeforeMonth_succ (year month : Nat) (positive : 0 < month) :
    daysBeforeMonth year (month + 1) = daysBeforeMonth year month + daysInMonth year month := by
  rw [daysBeforeMonth_eq_sum, daysBeforeMonth_eq_sum,
    show month + 1 - 1 = (month - 1) + 1 by omega, List.range_succ]
  simp [show month - 1 + 1 = month by omega]

theorem daysBeforeMonth_thirteen (year : Nat) :
    daysBeforeMonth year 13 = daysInYear year := by
  simp [daysBeforeMonth, List.range_succ, daysInMonth, daysInYear]
  split <;> rfl

theorem daysBeforeYear_monotone : Monotone daysBeforeYear := by
  apply monotone_nat_of_le_succ
  intro year
  by_cases afterEpoch : 1900 ≤ year
  · rw [daysBeforeYear_succ year afterEpoch]
    omega
  · have before : year - 1900 = 0 := by omega
    simp [daysBeforeYear, before]

theorem daysBeforeMonth_monotone (year : Nat) : Monotone (daysBeforeMonth year) := by
  apply monotone_nat_of_le_succ
  intro month
  cases month with
  | zero => simp [daysBeforeMonth]
  | succ month => rw [daysBeforeMonth_succ year (month + 1) (by omega)]; omega

theorem daysBeforeMonth_lt_year (year month : Nat) (positive : 0 < month) (bound : month ≤ 12) :
    daysBeforeMonth year month < daysInYear year := by
  have next := daysBeforeMonth_monotone year (show month + 1 ≤ 13 by omega)
  rw [daysBeforeMonth_succ year month positive, daysBeforeMonth_thirteen] at next
  have := daysInMonth_bounds year month positive bound
  omega

theorem firstOfMonth_succ (year month : Nat) (positive : 0 < month) :
    dayOfWeek year (month + 1) 1 =
      (dayOfWeek year month 1 + daysInMonth year month) % 7 := by
  simp only [dayOfWeek, Nat.sub_self, Nat.add_zero, daysBeforeMonth_succ year month positive]
  omega

theorem firstOfYear_succ (year : Nat) (afterEpoch : 1900 ≤ year) :
    dayOfWeek (year + 1) 1 1 = (dayOfWeek year 12 1 + daysInMonth year 12) % 7 := by
  have lastMonth := daysBeforeMonth_succ year 12 (by decide)
  rw [daysBeforeMonth_thirteen] at lastMonth
  simp only [dayOfWeek, Nat.sub_self, Nat.add_zero, daysBeforeMonth_one,
    daysBeforeYear_succ year afterEpoch]
  omega

theorem firstOfYear_after_months (year : Nat) (afterEpoch : 1900 ≤ year) :
    dayOfWeek year 13 1 = dayOfWeek (year + 1) 1 1 := by
  simp [dayOfWeek, daysBeforeMonth_thirteen, daysBeforeYear_succ year afterEpoch]

/-- Endpoints for comparing date-interval and whole-year counting interfaces. -/
def firstOfYear (year : Nat) : Date := mkFirstOfMonth year 1 (by decide) (by decide)

def lastOfYear (year : Nat) : Date :=
  mkDate year 12 31 (by decide) (by decide) (by decide) (by rfl)

@[simp] theorem dateToDays_firstOfYear (year : Nat) :
    dateToDays (firstOfYear year) = daysBeforeYear year := by
  simp [dateToDays, firstOfYear, mkFirstOfMonth]

theorem dateToDays_lastOfYear (year : Nat) :
    dateToDays (lastOfYear year) = daysBeforeYear year + daysInYear year - 1 := by
  have lastMonth := daysBeforeMonth_succ year 12 (by decide)
  rw [daysBeforeMonth_thirteen] at lastMonth
  simp only [dateToDays, lastOfYear, mkDate, daysInMonth] at *
  omega

theorem firstOfMonth_in_years (startYear endYear year month : Nat)
    (afterEpoch : 1900 ≤ startYear) (lower : startYear ≤ year) (upper : year ≤ endYear)
    (positive : 0 < month) (bound : month ≤ 12) :
    dateToDays (firstOfYear startYear) ≤ daysBeforeYear year + daysBeforeMonth year month ∧
      daysBeforeYear year + daysBeforeMonth year month ≤ dateToDays (lastOfYear endYear) := by
  rw [dateToDays_firstOfYear, dateToDays_lastOfYear]
  have start := daysBeforeYear_monotone lower
  have next := daysBeforeYear_monotone (show year + 1 ≤ endYear + 1 by omega)
  rw [daysBeforeYear_succ year (by omega), daysBeforeYear_succ endYear (by omega)] at next
  have within := daysBeforeMonth_lt_year year month positive bound
  omega

/-- Count Sundays among consecutive first days of months. -/
def sundaysInMonths (year first count : Nat) : Nat :=
  ((List.range count).map (fun i => if dayOfWeek year (first + i) 1 = 6 then 1 else 0)).sum

def sundaysInYear (year : Nat) : Nat := sundaysInMonths year 1 12

/-- The count is a length, so zero denotes the empty interval. -/
def sundaysInYears (first count : Nat) : Nat :=
  ((List.range count).map (fun i => sundaysInYear (first + i))).sum

/-- Scan from an earlier epoch while counting only years at or above a lower bound. -/
def eligibleYears (lower first count : Nat) : Nat :=
  ((List.range count).map (fun i => if lower ≤ first + i then sundaysInYear (first + i) else 0)).sum

@[simp] theorem eligibleYears_zero (lower first : Nat) : eligibleYears lower first 0 = 0 := rfl

theorem eligibleYears_succ (lower first count : Nat) :
    eligibleYears lower first (count + 1) = (if lower ≤ first then sundaysInYear first else 0) +
      eligibleYears lower (first + 1) count := by
  unfold eligibleYears
  rw [show count + 1 = 1 + count by omega, List.range_add]
  simp [List.range_succ, List.map_map, Function.comp_def, Nat.add_assoc]

theorem eligibleYears_after (lower first count : Nat) (eligible : lower ≤ first) :
    eligibleYears lower first count = sundaysInYears first count := by
  unfold eligibleYears sundaysInYears
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  exact if_pos (by omega)

theorem eligibleYears_before (lower first stop : Nat) (before : first ≤ lower) (nonempty : lower ≤ stop) :
    eligibleYears lower first (stop - first) = sundaysInYears lower (stop - lower) := by
  induction measure : lower - first using Nat.strong_induction_on generalizing first with
  | h remaining ih =>
      by_cases reached : lower ≤ first
      · have same : first = lower := by omega
        subst first
        exact eligibleYears_after lower lower (stop - lower) (by omega)
      · rw [show stop - first = (stop - (first + 1)) + 1 by omega, eligibleYears_succ, if_neg reached, Nat.zero_add]
        exact ih (lower - (first + 1)) (by omega) (first + 1) (by omega) rfl

@[simp] theorem sundaysInMonths_zero (year first : Nat) : sundaysInMonths year first 0 = 0 := rfl

@[simp] theorem sundaysInYears_zero (first : Nat) : sundaysInYears first 0 = 0 := rfl

theorem sundaysInMonths_succ (year first count : Nat) :
    sundaysInMonths year first (count + 1) =
      (if dayOfWeek year first 1 = 6 then 1 else 0) + sundaysInMonths year (first + 1) count := by
  unfold sundaysInMonths
  rw [show count + 1 = 1 + count by omega, List.range_add]
  simp [List.range_succ, List.map_map, Function.comp_def, Nat.add_assoc]

theorem sundaysInYears_succ (first count : Nat) :
    sundaysInYears first (count + 1) = sundaysInYear first + sundaysInYears (first + 1) count := by
  unfold sundaysInYears
  rw [show count + 1 = 1 + count by omega, List.range_add]
  simp [List.range_succ, List.map_map, Function.comp_def, Nat.add_assoc]

private theorem foldl_eq_add_sum (xs : List α) (f : Nat → α → Nat) (g : α → Nat)
    (step : ∀ x ∈ xs, ∀ acc, f acc x = acc + g x) (initial : Nat) :
    xs.foldl f initial = initial + (xs.map g).sum := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, step x (by simp)]
      rw [ih (fun y member => step y (by simp [member]))]
      simp [Nat.add_assoc]

theorem naive_whole_years (startYear endYear : Nat)
    (afterEpoch : 1900 ≤ startYear) (ordered : startYear ≤ endYear) :
    naive (firstOfYear startYear) (lastOfYear endYear) =
      sundaysInYears startYear (endYear + 1 - startYear) := by
  unfold naive countSundaysBetween
  change (List.range (endYear - startYear + 1)).foldl _ 0 = _
  have months (year : Nat) (lower : startYear ≤ year) (upper : year ≤ endYear) :
      (List.range 12).foldl (fun acc j =>
        if dateToDays (firstOfYear startYear) ≤ daysBeforeYear year + daysBeforeMonth year (j + 1) ∧
            daysBeforeYear year + daysBeforeMonth year (j + 1) ≤ dateToDays (lastOfYear endYear) ∧
            dayOfWeek year (j + 1) 1 = 6 then acc + 1 else acc) 0 = sundaysInYear year := by
    rw [foldl_eq_add_sum _ _ (fun j => if dayOfWeek year (j + 1) 1 = 6 then 1 else 0)]
    · simp [sundaysInYear, sundaysInMonths, Nat.add_comm]
    · intro j member acc
      have jBound := List.mem_range.mp member
      have within := firstOfMonth_in_years startYear endYear year (j + 1)
        afterEpoch lower upper (by omega) (by omega)
      simp only [within.1, within.2, true_and]
      split <;> simp
  rw [foldl_eq_add_sum _ _ (fun i => sundaysInYear (startYear + i))]
  · simp [sundaysInYears, show endYear - startYear + 1 = endYear + 1 - startYear by omega]
  · intro i member acc
    have iBound := List.mem_range.mp member
    exact congrArg (acc + ·) (months (startYear + i) (by omega) (by omega))

theorem intervalSunday_whole_years (startYear endYear year month : Nat)
    (afterEpoch : 1900 ≤ startYear) (lower : startYear ≤ year) (upper : year ≤ endYear)
    (positive : 0 < month) (bound : month ≤ 12) :
    intervalSunday (dateOrdinalInt startYear 1 1) (dateOrdinalInt endYear 12 31) year month =
      decide (dayOfWeek year month 1 = 6) := by
  have firstEq := dateOrdinalInt_date (firstOfYear startYear)
  have lastEq := dateOrdinalInt_date (lastOfYear endYear)
  change dateOrdinalInt startYear 1 1 = (dateToDays (firstOfYear startYear) : Int) at firstEq
  change dateOrdinalInt endYear 12 31 = (dateToDays (lastOfYear endYear) : Int) at lastEq
  have within := firstOfMonth_in_years startYear endYear year month afterEpoch lower upper positive bound
  have pointEq : dateOrdinalInt year month 1 = ((daysBeforeYear year + daysBeforeMonth year month : Nat) : Int) := by
    simpa only [Nat.cast_one, Nat.sub_self, Nat.add_zero] using dateOrdinalInt_nat year month 1 (by decide)
  have weekdayEq : dayOfWeekInt year month 1 = (dayOfWeek year month 1 : Int) := by
    simpa only [Nat.cast_one] using dayOfWeekInt_nat year month 1 (by decide)
  have withinInt : dateOrdinalInt startYear 1 1 ≤ dateOrdinalInt year month 1 ∧
      dateOrdinalInt year month 1 ≤ dateOrdinalInt endYear 12 31 := by
    rw [firstEq, lastEq, pointEq]
    exact_mod_cast within
  simp only [intervalSunday, withinInt.1, withinInt.2, true_and, weekdayEq]
  norm_cast

theorem intervalMonths_whole_years (startYear endYear year : Nat)
    (afterEpoch : 1900 ≤ startYear) (lower : startYear ≤ year) (upper : year ≤ endYear) :
    intervalMonths (dateOrdinalInt startYear 1 1) (dateOrdinalInt endYear 12 31) year 1 12 =
      (sundaysInYear year : Int) := by
  simp only [intervalMonths, sundaysInYear, sundaysInMonths, Nat.cast_list_sum, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i member
  rw [intervalSunday_whole_years startYear endYear year (1 + i) afterEpoch lower upper
    (by omega) (by have := List.mem_range.mp member; omega)]
  simp only [decide_eq_true_eq]
  split <;> rfl

theorem countSundaysInt_whole_years (startYear endYear : Nat)
    (afterEpoch : 1900 ≤ startYear) (ordered : startYear ≤ endYear) :
    countSundaysInt startYear 1 1 endYear 12 31 =
      (sundaysInYears startYear (endYear + 1 - startYear) : Int) := by
  have count : ((endYear : Int) + 1 - startYear).toNat = endYear + 1 - startYear := by omega
  simp only [countSundaysInt, intervalYears, count, sundaysInYears, Nat.cast_list_sum, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i member
  have inside := List.mem_range.mp member
  rw [show (startYear : Int) + i = ((startYear + i : Nat) : Int) by simp]
  exact intervalMonths_whole_years startYear endYear (startYear + i) afterEpoch (by omega) (by omega)

end ProjectEulerStatements.P19
