from math import comb


def naive(n: int) -> int:
    return comb(2 * n, n)


if __name__ == '__main__':
    assert naive(2) == 6

