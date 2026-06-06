from common import is_prime


def naive(n: int) -> int:
    if n == 0:
        return 0
    count = 0
    x = 1
    while count < n:
        x += 1
        if is_prime(x):
            count += 1
    return x


def primes_up_to(n: int) -> set[int]:
    return {x for x in range(n + 1) if is_prime(x)}


if __name__ == '__main__':
    assert len(primes_up_to(13)) == 6
    assert max(primes_up_to(13)) == 13

