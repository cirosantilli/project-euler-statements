from math import isqrt


def is_square(n: int) -> bool:
    r = isqrt(n)
    return r * r == n


def minimal_x(d: int) -> int:
    if is_square(d):
        return 0
    for y in range(1, d ** 4 + 2):
        x2 = d * y * y + 1
        x = isqrt(x2)
        if x * x == x2:
            return x
    return 0


def naive(limit: int) -> int:
    best_d = best_x = 0
    for d in range(2, limit + 1):
        x = minimal_x(d)
        if x > best_x:
            best_d, best_x = d, x
    return best_d


if __name__ == '__main__':
    assert minimal_x(13) == 649
    assert naive(7) == 5

