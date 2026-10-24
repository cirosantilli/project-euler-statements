from .common import digits_be, of_digits_be, is_prime


def truncations(n: int) -> list[int]:
    ds = digits_be(n)
    l = len(ds)
    return [of_digits_be(ds[i + 1:]) for i in range(l - 1)] + [of_digits_be(ds[:l - i - 1]) for i in range(l - 1)]


def is_truncatable_prime(n: int) -> bool:
    return n > 7 and is_prime(n) and all(is_prime(x) for x in truncations(n))


def naive(limit: int) -> int:
    """
    @formalsw: Requires(limit >= 0)
    @formalsw: Returns
    """
    return sum(n for n in range(limit) if is_truncatable_prime(n))


def naive_default() -> int:
    """
    @formalsw: Returns
    """
    return naive(1_000_000)


if __name__ == '__main__':
    assert is_truncatable_prime(3797)

