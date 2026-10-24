from .common import digits_le


def digits_sorted(n: int) -> list[int]:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    return sorted(digits_le(n))


def same_digits(a: int, b: int) -> bool:
    """
    @formalsw: Requires(a >= 0 and b >= 0)
    @formalsw: Returns
    """
    return digits_sorted(a) == digits_sorted(b)


def has_permuted_multiples(n: int, x: int) -> bool:
    """
    @formalsw: Requires(x >= 0)
    @formalsw: Returns
    """
    return n >= 2 and all(same_digits(x, (i + 2) * x) for i in range(n - 1))


def naive(n: int) -> int:
    """
    @formalsw: Requires(n >= 2)
    @formalsw: Requires(n <= 6)
    @formalsw: Returns
    """
    x = 1
    while True:
        if has_permuted_multiples(n, x):
            return x
        x += 1


if __name__ == '__main__':
    assert same_digits(125874, 2 * 125874)
    assert naive(2) == 125874
    assert naive(6) == 142857

