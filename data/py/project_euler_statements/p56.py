from .common import digits_le


def digit_sum(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return sum(digits_le(n))


def naive(n: int) -> int:
    """
    @formalsw: Returns
    """
    return max((digit_sum(a ** b) for a in range(n) for b in range(n)), default=0)

