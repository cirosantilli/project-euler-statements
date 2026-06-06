from common import is_prime


def is_prime_factor(n: int, k: int) -> bool:
    return 2 <= k and n % k == 0 and is_prime(k)


def naive(n: int) -> int:
    for k in range(n, 1, -1):
        if is_prime_factor(n, k):
            return k
    return 0


if __name__ == '__main__':
    assert naive(13195) == 29

