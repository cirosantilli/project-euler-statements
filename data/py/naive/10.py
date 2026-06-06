from common import is_prime


def naive(n: int) -> int:
    return sum(p for p in range(n) if is_prime(p))


if __name__ == '__main__':
    assert naive(10) == 17

