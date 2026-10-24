from .common import digits_be, of_digits_be, is_prime


def truncations(n: int) -> list[int]:
    ds = digits_be(n)
    l = len(ds)
    return [of_digits_be(ds[i + 1:]) for i in range(l - 1)] + [of_digits_be(ds[:l - i - 1]) for i in range(l - 1)]


def is_truncatable_prime(n: int) -> bool:
    return n > 7 and is_prime(n) and all(is_prime(x) for x in truncations(n))


def naive() -> int:
    """
    Exhaust the right-truncatable-prime tree, retaining primes truncatable from both ends.
    """
    frontier = [2, 3, 5, 7]
    total = 0
    while frontier:
        following = []
        for prefix in frontier:
            for digit in [1, 3, 7, 9]:
                candidate = 10 * prefix + digit
                if is_prime(candidate):
                    following.append(candidate)
                    if is_truncatable_prime(candidate):
                        total += candidate
        frontier = following
    return total


def naive_default() -> int:
    return naive()


if __name__ == '__main__':
    assert is_truncatable_prime(3797)

