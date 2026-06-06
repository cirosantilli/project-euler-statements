from math import gcd


def better_frac(a: int, b: int, c: int, d: int) -> bool:
    return a * d > c * b


def is_reduced(n: int, d: int) -> bool:
    return gcd(n, d) == 1


def left_of(limit: int, num: int, den: int) -> int:
    best_n, best_d = 0, 1
    for d in range(limit, 0, -1):
        for n in range(d):
            if n < d and is_reduced(n, d) and n * den < num * d and better_frac(n, d, best_n, best_d):
                best_n, best_d = n, d
    return best_n


def naive(limit: int) -> int:
    return left_of(limit, 3, 7)


if __name__ == '__main__':
    assert naive(8) == 2

