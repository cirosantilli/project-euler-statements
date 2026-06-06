def mod_pow(a: int, b: int, m: int) -> int:
    acc = 1
    a %= m
    for _ in range(b):
        acc = acc * a % m
    return acc


def series_mod(n: int, m: int) -> int:
    acc = 0
    for i in range(n):
        acc = (acc + mod_pow(i + 1, i + 1, m)) % m
    return acc


def naive(n: int) -> int:
    return series_mod(n, 10 ** 10)


if __name__ == '__main__':
    assert series_mod(10, 10 ** 10) == 10405071317 % (10 ** 10)

