from .common import digits_be, of_digits_be, is_prime


def truncations(n: int, base: int = 10) -> list[int]:
    digits = digits_be(n, base)
    width = len(digits)
    return (
        [of_digits_be(digits[i + 1:], base) for i in range(width - 1)]
        + [of_digits_be(digits[:width - i - 1], base) for i in range(width - 1)]
    )


def is_truncatable_prime(n: int, base: int = 10) -> bool:
    return n >= base and is_prime(n) and all(is_prime(x) for x in truncations(n, base))


def naive(base: int = 10) -> int:
    """
    Exhaust the right-truncatable-prime tree, retaining primes truncatable from both ends.

    @formalsw: Requires(base >= 2)
    @formalsw: theorem supported : (this_function base).Supported
    """
    frontier = [n for n in range(2, base) if is_prime(n)]
    total = 0
    while frontier:
        following = []
        for prefix in frontier:
            for digit in range(1, base):
                candidate = base * prefix + digit
                if is_prime(candidate):
                    following.append(candidate)
                    if is_truncatable_prime(candidate, base):
                        total += candidate
        frontier = following
    return total


def naive_default() -> int:
    return naive()


if __name__ == '__main__':
    assert is_truncatable_prime(3797)

