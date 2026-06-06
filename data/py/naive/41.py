from itertools import permutations
from common import digits_be, of_digits_be, is_prime


def is_pandigital_n(n: int, x: int) -> bool:
    ds = digits_be(x)
    return len(ds) == n and len(set(ds)) == n and all(1 <= d <= n for d in ds)


def naive(n: int) -> int:
    nums = [of_digits_be(list(p)) for p in permutations(range(1, n + 1))]
    vals = [x for x in nums if is_prime(x)]
    return max(vals) if vals else 0


if __name__ == '__main__':
    assert is_pandigital_n(4, 2143)
    assert is_prime(2143)

