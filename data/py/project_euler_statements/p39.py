def count_solutions(p: int) -> int:
    c = 0
    for a in range(p + 1):
        for b in range(p + 1):
            cc = p - a - b
            if a < b < cc and a * a + b * b == cc * cc:
                c += 1
    return c


def naive(limit: int) -> int:
    return max(range(limit + 1), key=count_solutions) if limit >= 0 else 0


if __name__ == '__main__':
    assert count_solutions(120) == 3

