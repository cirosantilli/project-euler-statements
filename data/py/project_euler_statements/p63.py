from .common import digits_le


def num_digits(n: int, base: int = 10) -> int:
    return len(digits_le(n, base))


def naive(base: int = 10) -> int:
    """
    @formalsw: Requires(base >= 2)
    @formalsw: Returns
    """
    total = 0
    n = 1
    while num_digits((base - 1) ** n, base) >= n:
        for a in range(1, base):
            if num_digits(a ** n, base) == n:
                total += 1
        n += 1
    return total


def naive_default() -> int:
    return naive()


if __name__ == "__main__":
    assert num_digits(7 ** 5) == 5
    assert num_digits(8 ** 9) == 9
    assert num_digits(2 ** 3, 2) == 4
    assert naive(2) == 1
    assert naive(3) == 3
    assert naive_default() == 49
