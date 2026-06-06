def rect_count(m: int, n: int) -> int:
    return (m * (m + 1) // 2) * (n * (n + 1) // 2)


def naive(target: int, limit: int) -> int:
    best_area, best_diff = 0, target
    for m in range(limit, 0, -1):
        for n in range(limit, -1, -1):
            count = rect_count(m, n)
            diff = count - target if count >= target else target - count
            if diff < best_diff:
                best_area, best_diff = m * n, diff
    return best_area


if __name__ == '__main__':
    assert rect_count(3, 2) == 18

