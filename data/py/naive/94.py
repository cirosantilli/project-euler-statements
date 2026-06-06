from math import isqrt


def is_square(n: int) -> bool:
    r = isqrt(n)
    return r * r == n


def area_is_int(a: int, b: int, c: int) -> bool:
    s = a + b + c
    if s % 2 == 1:
        return False
    p = s // 2
    return is_square(p * (p - a) * (p - b) * (p - c))


def naive(limit: int) -> int:
    acc = 0
    for a in range(limit + 1):
        c1, c2 = a - 1, a + 1
        if a > 1 and c1 > 0 and area_is_int(a, a, c1):
            acc += a + a + c1
        if area_is_int(a, a, c2):
            acc += a + a + c2
    return acc


if __name__ == '__main__':
    assert area_is_int(5, 5, 6)

