from common import digits_be


def champernowne_digits(limit: int) -> list[int]:
    out = []
    for i in range(limit):
        out += digits_be(i + 1)
    return out


def digit_at(n: int, limit: int) -> int:
    ds = champernowne_digits(limit)
    return ds[n - 1] if 0 <= n - 1 < len(ds) else 0


def naive(limit: int) -> int:
    acc = 1
    for i in [1, 10, 100, 1000, 10000, 100000, 1000000]:
        acc *= digit_at(i, limit)
    return acc


if __name__ == '__main__':
    assert digit_at(12, 20) == 1

