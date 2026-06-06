from math import factorial
from common import digits_le


def digit_fact_sum(n: int) -> int:
    return sum(factorial(d) for d in digits_le(n))


def naive(limit: int) -> int:
    return sum(n for n in range(limit + 1) if n not in (1, 2) and digit_fact_sum(n) == n)


if __name__ == '__main__':
    assert digit_fact_sum(145) == 145

