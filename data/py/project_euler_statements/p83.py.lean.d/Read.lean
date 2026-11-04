import data.«project-euler-statements».data.py.project_euler_statements.«p83.py.lean.d».Dimensions

namespace data.«project-euler-statements».data.py.project_euler_statements.p83
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RectangularMatrixCalls
open ProjectEulerSolutions.TriangleBufferCalls (number)
open ProjectEulerStatements.P83 (getD2)
set_option Elab.async false

abbrev readArgs : List Arg := arguments ++
  [⟨"r", some (.name "int"), none⟩, ⟨"c", some (.name "int"), none⟩]
abbrev rowExpr : Expr := .subscript (.name "matrix") (.name "r")
abbrev rowTest : Expr := .compare (.constant (.int 0))
  [(.ltE, .name "r"), (.lt, .builtinCall .len [.name "matrix"])]
abbrev colTest : Expr := .compare (.constant (.int 0))
  [(.ltE, .name "c"), (.lt, .builtinCall .len [rowExpr])]

theorem bounds_test (heap : Mutable.Heap) (env : HeapCalls.Env) (index size : Int)
    (indexExpr sizeExpr : Expr)
    (indexValue : Evaluates program env indexExpr heap (number index) heap)
    (sizeValue : Evaluates program env sizeExpr heap (number size) heap) :
    Evaluates program env (.compare (.constant (.int 0)) [(.ltE, indexExpr), (.lt, sizeExpr)])
      heap (.scalar (.bool (decide (0 ≤ index ∧ index < size)))) heap := by
  apply Evaluates.chain Evaluates.constant
  by_cases nonnegative : 0 ≤ index
  · apply Evaluates.Compares.next (afterComparison := heap) (compared := .scalar (.bool true)) indexValue
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, nonnegative]) rfl
    apply Evaluates.Compares.last sizeValue
    simp [HeapCalls.compare, scalarCompare, evalCmpOp, nonnegative]
  · simp only [nonnegative, false_and, decide_false]
    apply Evaluates.Compares.stop indexValue
      (by simp [HeapCalls.compare, scalarCompare, evalCmpOp, nonnegative]) rfl

theorem get_d2.result (heap : Mutable.Heap) (address : Nat) (rows : MatrixRows) (r c : Int)
    (found : heap[address]? = some (.list (rows.map (fun pair => .ref pair.1))))
    (reads : ∀ pair ∈ rows, heap[pair.1]? = some (.list (encode pair.2))) :
    ReturnsValue program "get_d2" [.ref address, number r, number c] heap
      (number (getD2 (rows.map Prod.snd) r c)) heap := by
  let entry := argumentEnv readArgs [.ref address, number r, number c]
  have height : Evaluates program entry (.builtinCall .len [.name "matrix"])
      heap (number rows.length) heap := by
    apply Evaluates.builtin (.cons (Evaluates.lookup rfl) .nil)
    simp [HeapCalls.primitive, Mutable.length, found]
  have testedRow := bounds_test heap entry r rows.length (.name "r") (.builtinCall .len [.name "matrix"])
    (Evaluates.lookup rfl) height
  apply BlockReturns.function (args := readArgs) rfl rfl
  apply BlockReturns.return_value
  by_cases rowInside : 0 ≤ r ∧ r < rows.length
  · have ri : r.toNat < rows.length := by omega
    have rnat : (r.toNat : Int) = r := by omega
    let pair := rows[r.toNat]
    have readRow : Evaluates program entry rowExpr heap (.ref pair.1) heap := by
      apply Evaluates.subscript (by intros a b c impossible; cases impossible)
        (Evaluates.lookup rfl) (Evaluates.lookup rfl)
      have result := Mutable.getItem_list heap address r.toNat (rows.map (fun pair => .ref pair.1))
        found (by simpa using ri)
      simpa only [List.getElem_map, rnat] using result
    have width : Evaluates program entry (.builtinCall .len [rowExpr]) heap (number pair.2.length) heap := by
      apply Evaluates.builtin (.cons readRow .nil)
      simp [HeapCalls.primitive, Mutable.length, reads pair (List.getElem_mem ri), encode]
    have testedCol := bounds_test heap entry c pair.2.length (.name "c") (.builtinCall .len [rowExpr])
      (Evaluates.lookup rfl) width
    have combined : Evaluates program entry (.boolOp .and [rowTest, colTest]) heap
        (.scalar (.bool (decide (0 ≤ c ∧ c < pair.2.length)))) heap := by
      apply Evaluates.boolean_next (flag := true) (value := .scalar (.bool true))
        (by simpa only [rowInside, and_self, decide_true] using testedRow) rfl rfl
      exact Evaluates.boolean_last testedCol rfl
    by_cases colInside : 0 ≤ c ∧ c < pair.2.length
    · have ci : c.toNat < pair.2.length := by omega
      have cnat : (c.toNat : Int) = c := by omega
      apply Evaluates.conditional (flag := true) (by simpa only [colInside, and_self, decide_true] using combined) rfl
      apply Evaluates.subscript (by intros a b c impossible; cases impossible) readRow (Evaluates.lookup rfl)
      have result := Mutable.getItem_list heap pair.1 c.toNat (encode pair.2)
        (reads pair (List.getElem_mem ri)) (by simpa [encode] using ci)
      simpa [getD2, rowInside.1, colInside.1, List.getD, List.getElem?_eq_getElem ri,
        List.getElem?_eq_getElem ci, encode, cnat, pair] using result
    · apply Evaluates.conditional (flag := false) (by simpa only [colInside, decide_false] using combined) rfl
      have zero : getD2 (rows.map Prod.snd) r c = 0 := by
        by_cases negative : c < 0
        · simp [getD2, show ¬ 0 ≤ c by omega]
        · have outside : pair.2.length ≤ c.toNat := by omega
          simp [getD2, rowInside.1, show 0 ≤ c by omega, List.getD,
            List.getElem?_eq_getElem ri, pair,
            List.getElem?_eq_none outside]
      rw [zero]
      exact Evaluates.constant
  · have combined : Evaluates program entry (.boolOp .and [rowTest, colTest]) heap
        (.scalar (.bool false)) heap :=
      Evaluates.boolean_stop (by simpa only [rowInside, decide_false] using testedRow) rfl rfl
    apply Evaluates.conditional (flag := false) combined rfl
    have zero : getD2 (rows.map Prod.snd) r c = 0 := by
      by_cases negative : r < 0
      · simp [getD2, show ¬ 0 ≤ r by omega]
      · have outside : rows.length ≤ r.toNat := by omega
        simp [getD2, List.getD, List.getElem?_eq_none outside]
    rw [zero]
    exact Evaluates.constant

end data.«project-euler-statements».data.py.project_euler_statements.p83
