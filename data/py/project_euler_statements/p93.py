"""
@formalsw: theorem eval_ops_source (a b : ProjectEulerSolutions.RationalPair.Pair)
  (left right : Nat) (heap : FormalSW.PyAst.Mutable.Heap) (globals : FormalSW.PyAst.Mutable.Globals) :
  heap[left]? = some (ProjectEulerSolutions.RationalPair.Heap.object a) →
    heap[right]? = some (ProjectEulerSolutions.RationalPair.Heap.object b) →
      data.«project-euler-statements».data.py.project_euler_statements.p93.eval_ops.Verified a b left right heap globals
@formalsw: theorem all_results_source (xs : List Int) (address : Nat)
  (heap : FormalSW.PyAst.Mutable.Heap) (globals : FormalSW.PyAst.Mutable.Globals) :
  heap[address]? = some (.tuple (xs.map ProjectEulerSolutions.RationalPair.Heap.number)) →
    data.«project-euler-statements».data.py.project_euler_statements.p93.all_results.Computed xs address heap globals
@formalsw: theorem consecutive_for_digits_source (xs : List Int) (address : Nat)
  (heap : FormalSW.PyAst.Mutable.Heap) (globals : FormalSW.PyAst.Mutable.Globals) :
  heap[address]? = some (.tuple (xs.map ProjectEulerSolutions.RationalPair.Heap.number)) →
    ∃ extra, FormalSW.PyAst.HeapCalls.ReturnsValue P93Ast.module "consecutive_for_digits" [.ref address] heap
      (ProjectEulerSolutions.RationalPair.Heap.number
        (data.«project-euler-statements».data.py.project_euler_statements.p93.consecutive_for_digits.runLength xs))
      (heap ++ extra) globals
@formalsw: theorem naive_source (bound : Int)
  (heap : FormalSW.PyAst.Mutable.Heap) (globals : FormalSW.PyAst.Mutable.Globals) :
  data.«project-euler-statements».data.py.project_euler_statements.p93.naive.Verified bound heap globals
"""

from itertools import combinations, permutations


def eval_ops(a: tuple[int, int], b: tuple[int, int]) -> list[tuple[int, int]]:
    numerator_a, denominator_a = a
    numerator_b, denominator_b = b
    denominator = denominator_a * denominator_b
    out = [
        (numerator_a * denominator_b + numerator_b * denominator_a, denominator),
        (numerator_a * denominator_b - numerator_b * denominator_a, denominator),
        (numerator_a * numerator_b, denominator),
    ]
    if numerator_b > 0:
        out.append((numerator_a * denominator_b, denominator_a * numerator_b))
    elif numerator_b < 0:
        out.append((-numerator_a * denominator_b, -denominator_a * numerator_b))
    return out


def all_results(nums: tuple[int, ...]) -> list[tuple[int, int]]:
    if not nums:
        return []
    if len(nums) == 1:
        return [(nums[0], 1)]
    out = []
    for split in range(1, len(nums)):
        left = all_results(nums[:split])
        right = all_results(nums[split:])
        for a in left:
            for b in right:
                out.extend(eval_ops(a, b))
    return out


def consecutive_count(xs: list[int]) -> int:
    """
    @formalsw: Returns
    @formalsw: ReturnType
    """
    n = 1
    while n in xs:
        n += 1
    return n - 1


def consecutive_for_digits(digits: tuple[int, ...]) -> int:
    integers = []
    for order in permutations(digits):
        for numerator, denominator in all_results(order):
            if numerator > 0 and numerator % denominator == 0:
                integers.append(numerator // denominator)
    return consecutive_count(integers)


def naive(max_digit: int = 9) -> tuple[int, ...]:
    """
    @formalsw: Returns
    """
    best_length = -1
    best_digits = ()
    for digits in combinations(range(max_digit + 1), 4):
        length = consecutive_for_digits(digits)
        if length > best_length:
            best_length = length
            best_digits = digits
    return best_digits


if __name__ == "__main__":
    assert consecutive_for_digits((1, 2, 3, 4)) == 28
    assert consecutive_for_digits((1, 2, 5, 8)) == 51
    print("".join(map(str, naive())))
