from math import isqrt


def is_square(n: int) -> bool:
    r = isqrt(n)
    return r * r == n


def count_cuboids(m: int) -> int:
    acc = 0
    for a in range(m, 0, -1):
        for b in range(m, 0, -1):
            for c in range(m, 0, -1):
                if a <= b <= c and is_square((a + b) ** 2 + c ** 2):
                    acc += 1
    return acc


def naive(m: int) -> int:
    return count_cuboids(m)


if __name__ == '__main__':
    assert count_cuboids(100) == 2060
    assert count_cuboids(99) == 1975

