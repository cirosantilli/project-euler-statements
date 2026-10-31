from math import isqrt


def is_square(n: int) -> bool:
    r = isqrt(n)
    return r * r == n


def count_new_cuboids(c: int) -> int:
    acc = 0
    for a in range(1, c + 1):
        for b in range(a, c + 1):
            if is_square((a + b) ** 2 + c ** 2):
                acc += 1
    return acc


def count_cuboids(m: int) -> int:
    total = 0
    for c in range(1, m + 1):
        total += count_new_cuboids(c)
    return total


def naive(target: int) -> int:
    total = 0
    c = 0
    while total <= target:
        c += 1
        total += count_new_cuboids(c)
    return c


if __name__ == "__main__":
    assert count_cuboids(100) == 2060
    assert count_cuboids(99) == 1975
    assert naive(-1) == 0
    assert naive(0) == 3
    assert naive(2000) == 100

