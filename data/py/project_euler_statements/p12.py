from .common import divisors


def triangle(n: int) -> int:
    """
    @formalsw: Returns
    """
    return n * (n + 1) // 2


def divisor_count(n: int) -> int:
    """
    @formalsw: Returns
    """
    return len(divisors(n))


def naive(k: int) -> int:
    """
    @formalsw: Returns
    """
    n = 0
    while True:
        t = triangle(n)
        if divisor_count(t) > k:
            return t
        n += 1


if __name__ == '__main__':
    assert naive(5) == 28

