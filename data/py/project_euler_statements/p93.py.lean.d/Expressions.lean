import data.«project-euler-statements».«.formalsw».data.py.project_euler_statements.«p93.py.ast»
import ProjectEulerSolutions.Lib.RationalOperations
import ProjectEulerSolutions.Lib.RationalHeap

namespace data.«project-euler-statements».data.py.project_euler_statements.p93.eval_ops
open FormalSW.PyAst HeapCalls ProjectEulerSolutions.RationalPair
set_option Elab.async false

abbrev program := P93Ast.module
abbrev number := Heap.number
abbrev object := Heap.object

structure Ready (env : HeapCalls.Env) (a b : Pair) : Prop where
  numeratorA : env "numerator_a" = some (number a.1)
  denominatorA : env "denominator_a" = some (number a.2)
  numeratorB : env "numerator_b" = some (number b.1)
  denominatorB : env "denominator_b" = some (number b.2)
  denominator : env "denominator" = some (number (a.2 * b.2))

abbrev na : Expr := .name "numerator_a"
abbrev da : Expr := .name "denominator_a"
abbrev nb : Expr := .name "numerator_b"
abbrev db : Expr := .name "denominator_b"
abbrev denominator : Expr := .name "denominator"
abbrev crossA : Expr := .binOp na .mult db
abbrev crossB : Expr := .binOp nb .mult da
abbrev addExpr : Expr := .tuple [.binOp crossA .add crossB, denominator]
abbrev subExpr : Expr := .tuple [.binOp crossA .sub crossB, denominator]
abbrev mulExpr : Expr := .tuple [.binOp na .mult nb, denominator]
abbrev positiveExpr : Expr := .tuple [crossA, .binOp da .mult nb]
abbrev negativeExpr : Expr := .tuple [.binOp (.unaryOp .uSub na) .mult db, .binOp (.unaryOp .uSub da) .mult nb]

variable {env : HeapCalls.Env} {heap : Mutable.Heap} {globals : Mutable.Globals}
variable {left right : Expr} {x y : Int}

theorem times (a : Evaluates program env left heap (number x) heap globals)
    (b : Evaluates program env right heap (number y) heap globals) :
    Evaluates program env (.binOp left .mult right) heap (number (x * y)) heap globals :=
  Evaluates.binary a b (by simp [Mutable.binary, scalarBinary, number, Heap.number])

theorem plus (a : Evaluates program env left heap (number x) heap globals)
    (b : Evaluates program env right heap (number y) heap globals) :
    Evaluates program env (.binOp left .add right) heap (number (x + y)) heap globals :=
  Evaluates.binary a b (by simp [Mutable.binary, scalarBinary, number, Heap.number])

theorem minus (a : Evaluates program env left heap (number x) heap globals)
    (b : Evaluates program env right heap (number y) heap globals) :
    Evaluates program env (.binOp left .sub right) heap (number (x - y)) heap globals :=
  Evaluates.binary a b (by simp [Mutable.binary, scalarBinary, number, Heap.number])

theorem negate (a : Evaluates program env left heap (number x) heap globals) :
    Evaluates program env (.unaryOp .uSub left) heap (number (-x)) heap globals := Evaluates.unary a rfl

theorem pair (a : Evaluates program env left heap (number x) heap globals)
    (b : Evaluates program env right heap (number y) heap globals) :
    Evaluates program env (.tuple [left, right]) heap (.ref heap.length) (heap ++ [object (x,y)]) globals :=
  Evaluates.tuple (.cons a (.cons b .nil)) (by simp)

theorem addition (a b : Pair) (ready : Ready env a b) :
    Evaluates program env addExpr heap (.ref heap.length) (heap ++ [object (add a b)]) globals :=
  pair (plus (times (.lookup ready.numeratorA) (.lookup ready.denominatorB))
    (times (.lookup ready.numeratorB) (.lookup ready.denominatorA))) (.lookup ready.denominator)

theorem subtraction (a b : Pair) (ready : Ready env a b) :
    Evaluates program env subExpr heap (.ref heap.length) (heap ++ [object (sub a b)]) globals :=
  pair (minus (times (.lookup ready.numeratorA) (.lookup ready.denominatorB))
    (times (.lookup ready.numeratorB) (.lookup ready.denominatorA))) (.lookup ready.denominator)

theorem multiplication (a b : Pair) (ready : Ready env a b) :
    Evaluates program env mulExpr heap (.ref heap.length) (heap ++ [object (mul a b)]) globals :=
  pair (times (.lookup ready.numeratorA) (.lookup ready.numeratorB)) (.lookup ready.denominator)

theorem positive_pair (a b : Pair) (ready : Ready env a b) :
    Evaluates program env positiveExpr heap (.ref heap.length)
      (heap ++ [object (a.1*b.2, a.2*b.1)]) globals :=
  pair (times (.lookup ready.numeratorA) (.lookup ready.denominatorB))
    (times (.lookup ready.denominatorA) (.lookup ready.numeratorB))

theorem negative_pair (a b : Pair) (ready : Ready env a b) :
    Evaluates program env negativeExpr heap (.ref heap.length)
      (heap ++ [object (-a.1*b.2, -a.2*b.1)]) globals :=
  pair (times (negate (.lookup ready.numeratorA)) (.lookup ready.denominatorB))
    (times (negate (.lookup ready.denominatorA)) (.lookup ready.numeratorB))

end data.«project-euler-statements».data.py.project_euler_statements.p93.eval_ops
