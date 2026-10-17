from math import gcd


def naive(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    acc = 1
    for x in range(1, n + 1):
        acc = acc * x // gcd(acc, x)
    return acc


if __name__ == '__main__':
    assert naive(10) == 2520

