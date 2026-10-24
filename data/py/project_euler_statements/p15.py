from math import comb


def naive(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return comb(2 * n, n)


if __name__ == '__main__':
    assert naive(2) == 6

