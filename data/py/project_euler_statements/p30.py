from .common import digits_le


def digit_power_sum(p: int, n: int) -> int:
    return sum(d ** p for d in digits_le(n))


def limit(p: int) -> int:
    return (p + 2) * 9 ** p


def naive(p: int) -> int:
    """
    @formalsw: Requires(p >= 0)
    @formalsw: Returns
    """
    return sum(n for n in range(limit(p) + 1) if n != 1 and digit_power_sum(p, n) == n)


def naive_default() -> int:
    """
    @formalsw: Returns
    """
    return naive(5)

