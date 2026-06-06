from common import digits_le


def digit_sum(n: int) -> int:
    return sum(digits_le(n))


def naive(n: int) -> int:
    return max((digit_sum(a ** b) for a in range(n) for b in range(n)), default=0)

