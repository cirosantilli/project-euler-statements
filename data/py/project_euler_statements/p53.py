from math import comb


def naive(limit_n: int = 100, threshold: int = 1_000_000) -> int:
    return sum(
        1
        for n in range(1, limit_n + 1)
        for r in range(n + 1)
        if comb(n, r) > threshold
    )


if __name__ == '__main__':
    assert comb(5, 3) == 10
    assert comb(23, 10) == 1144066
    assert naive(1, 0) == 2
    assert naive() == 4075

