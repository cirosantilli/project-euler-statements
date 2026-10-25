def next_pair(b: int, t: int) -> tuple[int, int]:
    return 3 * b + 2 * t - 2, 4 * b + 3 * t - 3


def first_over(limit: int) -> int:
    b, t = 3, 4
    while t <= limit:
        b, t = next_pair(b, t)
    return b


def naive(limit: int) -> int:
    return first_over(limit)


if __name__ == '__main__':
    assert 2 * 15 * 14 == 21 * 20
    assert 2 * 85 * 84 == 120 * 119
    assert naive(-1) == 3
    assert naive(3) == 3
    assert naive(4) == 15
    assert naive(21) == 85

