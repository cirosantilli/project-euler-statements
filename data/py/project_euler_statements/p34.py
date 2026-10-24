from math import factorial
from .common import digits_le


def digit_fact_sum(n: int, base: int = 10) -> int:
    return sum(factorial(d) for d in digits_le(n, base))


def naive(base: int = 10) -> int:
    """
    Sum fixed points with at least two digits using a complete input-derived bound.

    @formalsw: Requires(base >= 2)
    @formalsw: Returns
    """
    digits = 1
    while base ** (digits - 1) <= digits * factorial(base - 1):
        digits += 1
    upper = (digits - 1) * factorial(base - 1)
    return sum(n for n in range(base, upper + 1) if digit_fact_sum(n, base) == n)


def naive_default() -> int:
    return naive()


if __name__ == '__main__':
    assert digit_fact_sum(145) == 145
