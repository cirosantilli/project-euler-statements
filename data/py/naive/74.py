from math import factorial
from common import digits_le


def next_term(n: int) -> int:
    return sum(factorial(d) for d in digits_le(n))


def chain_len(n: int) -> int:
    x, seen = n, []
    for _ in range(n + 1):
        if x in seen:
            return len(seen)
        seen.append(x)
        x = next_term(x)
    return len(seen)


def naive(limit: int, target: int) -> int:
    return sum(1 for n in range(limit) if chain_len(n) == target)


if __name__ == '__main__':
    assert chain_len(69) == 5
    assert chain_len(78) == 4
    assert chain_len(540) == 2

