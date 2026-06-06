def next_pair(b: int, t: int) -> tuple[int, int]:
    return 3 * b + 2 * t - 2, 4 * b + 3 * t - 3


def first_over(limit: int) -> int:
    b, t = 15, 21
    for _ in range(limit + 1):
        if t > limit:
            return b
        b, t = next_pair(b, t)
    return 0


def naive(limit: int) -> int:
    return first_over(limit)


if __name__ == '__main__':
    assert 2 * 15 * 14 == 21 * 20
    assert 2 * 85 * 84 == 120 * 119

