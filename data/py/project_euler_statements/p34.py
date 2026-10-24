from math import factorial
from .common import digits_le


def digit_fact_sum(n: int) -> int:
    return sum(factorial(d) for d in digits_le(n))


def naive() -> int:
    """
    Derive a complete search bound: a d-digit solution is at most d * 9!.
    """
    digits = 1
    while 10 ** (digits - 1) <= digits * factorial(9):
        digits += 1
    upper = (digits - 1) * factorial(9)
    return sum(n for n in range(upper + 1) if n not in (1, 2) and digit_fact_sum(n) == n)


def naive_default() -> int:
    return naive()


if __name__ == '__main__':
    assert digit_fact_sum(145) == 145

