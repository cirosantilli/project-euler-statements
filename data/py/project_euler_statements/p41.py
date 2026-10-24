import itertools
from .common import digits_be, of_digits_be, is_prime


def is_pandigital_n(n: int, x: int) -> bool:
    ds = digits_be(x)
    return len(ds) == n and len(set(ds)) == n and all(1 <= d <= n for d in ds)


def naive(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    digits = [i for i in range(1, n + 1)]
    nums = [of_digits_be(list(p)) for p in itertools.permutations(digits)]
    vals = [x for x in nums if is_prime(x)]
    return max(vals) if vals else 0


def naive_bound(max_digits: int) -> int:
    """
    @formalsw: Requires(max_digits >= 0)
    @formalsw: Returns
    """
    values = [naive(n) for n in range(1, max_digits + 1)]
    return max(values) if values else 0


if __name__ == '__main__':
    assert is_pandigital_n(4, 2143)
    assert is_prime(2143)

