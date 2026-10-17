from math import comb


def naive() -> int:
    return sum(1 for n in range(101) if n != 0 for r in range(n + 1) if comb(n, r) > 1000000)


if __name__ == '__main__':
    assert comb(5, 3) == 10
    assert comb(23, 10) == 1144066

