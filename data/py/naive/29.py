def powers(a_max: int, b_max: int) -> list[int]:
    return [a ** b for a in range(2, a_max + 1) for b in range(2, b_max + 1)]


def naive(a_max: int, b_max: int) -> int:
    return len(set(powers(a_max, b_max)))


if __name__ == '__main__':
    assert naive(5, 5) == 15

