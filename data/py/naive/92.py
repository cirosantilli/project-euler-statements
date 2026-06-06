from common import digits_le


def next_term(n: int) -> int:
    return sum(d * d for d in digits_le(n))


def ends_at_89(n: int) -> bool:
    x = n
    for _ in range(n + 1):
        if x == 1:
            return False
        if x == 89:
            return True
        x = next_term(x)
    return False


def naive(limit: int) -> int:
    return sum(1 for n in range(limit) if ends_at_89(n))


if __name__ == '__main__':
    assert not ends_at_89(44)
    assert ends_at_89(85)

