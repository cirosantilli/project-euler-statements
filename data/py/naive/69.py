from math import gcd


def phi(n: int) -> int:
    return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)


def better(a: int, b: int) -> bool:
    return False if phi(a) == 0 or phi(b) == 0 else a * phi(b) > b * phi(a)


def naive(limit: int) -> int:
    best = 1
    for n in range(limit + 1):
        if better(n, best):
            best = n
    return best


if __name__ == '__main__':
    assert phi(9) == 6
    assert naive(10) == 6

