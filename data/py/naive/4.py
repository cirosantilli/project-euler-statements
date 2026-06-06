from common import digits_le


def naive(n: int) -> int:
    lo = 0 if n == 0 else 10 ** (n - 1)
    hi = 10 ** n - 1
    max_ = 0
    for a in range(lo, hi + 1):
        for b in range(a, hi + 1):
            prod = a * b
            ds = digits_le(prod)
            if ds == list(reversed(ds)):
                max_ = max(prod, max_)
    return max_


if __name__ == '__main__':
    assert naive(2) == 9009
