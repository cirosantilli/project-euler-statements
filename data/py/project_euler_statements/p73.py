from math import gcd


def count_between(d: int, lower_num: int, lower_den: int, upper_num: int, upper_den: int) -> int:
    """
    @formalsw: Returns
    """
    return sum(
        1
        for n in range(1, d)
        if gcd(n, d) == 1 and n * lower_den > lower_num * d and n * upper_den < upper_num * d
    )


def naive(
    limit: int,
    lower_num: int = 1,
    lower_den: int = 3,
    upper_num: int = 1,
    upper_den: int = 2,
) -> int:
    """
    @formalsw: Requires(lower_den > 0)
    @formalsw: Requires(upper_den > 0)
    @formalsw: Returns
    """
    return sum(
        count_between(d, lower_num, lower_den, upper_num, upper_den)
        for d in range(2, limit + 1)
    )


if __name__ == "__main__":
    assert naive(8) == 3
