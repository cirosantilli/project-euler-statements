def rect_count(m: int, n: int) -> int:
    return (m * (m + 1) // 2) * (n * (n + 1) // 2)


def naive(target: int) -> int:
    best_area = 1
    best_diff = abs(1 - target)
    m = 1
    while rect_count(m, m) <= target + best_diff:
        n = m
        while rect_count(m, n) <= target + best_diff:
            diff = abs(rect_count(m, n) - target)
            if diff < best_diff:
                best_area, best_diff = m * n, diff
            n += 1
        m += 1
    return best_area


if __name__ == "__main__":
    assert rect_count(3, 2) == 18
    assert naive(0) == 1
    assert naive(18) == 6
    assert naive(2_000_000) == 2772
