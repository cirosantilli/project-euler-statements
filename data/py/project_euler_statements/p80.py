from math import isqrt
from .common import digits_le


def digit_sum(n: int) -> int:
    return sum(digits_le(n))


def is_square(n: int) -> bool:
    r = isqrt(n)
    return r * r == n


def sqrt_digits_sum(n: int, digits: int) -> int:
    if is_square(n):
        return 0
    root = isqrt(n)
    width = len(str(root))
    if digits < width:
        prefix = root // 10 ** (width - digits)
    else:
        prefix = isqrt(n * 10 ** (2 * (digits - width)))
    return digit_sum(prefix)


def naive(limit: int, digits: int) -> int:
    """
    @formalsw: Requires(limit >= 0)
    @formalsw: Requires(digits >= 1)
    @formalsw: Returns
    """
    return sum(sqrt_digits_sum(n, digits) for n in range(limit + 1))


if __name__ == '__main__':
    assert sqrt_digits_sum(2, 100) == 475

