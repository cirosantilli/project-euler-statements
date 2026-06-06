def count_solutions(p: int) -> int:
    return sum(1 for a in range(p + 1) for b in range(p + 1) if a < b < p - a - b and a * a + b * b == (p - a - b) ** 2)


def naive(limit: int) -> int:
    return sum(1 for p in range(limit + 1) if count_solutions(p) == 1)


if __name__ == '__main__':
    assert count_solutions(12) == 1
    assert count_solutions(120) == 3

