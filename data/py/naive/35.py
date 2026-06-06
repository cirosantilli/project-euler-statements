from common import digits_be, of_digits_be, is_prime


def rotations(xs: list[int]) -> list[list[int]]:
    return [xs[i:] + xs[:i] for i in range(len(xs))]


def is_circular_prime(n: int) -> bool:
    return n >= 2 and all(is_prime(of_digits_be(r)) for r in rotations(digits_be(n)))


def naive(limit: int) -> int:
    return sum(1 for n in range(limit) if is_circular_prime(n))


if __name__ == '__main__':
    assert is_circular_prime(197)
    assert naive(100) == 13

