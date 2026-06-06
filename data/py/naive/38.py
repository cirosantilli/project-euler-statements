from common import digits_be


def num_digits(n: int) -> int:
    return len(digits_be(n))


def concat_nat(a: int, b: int) -> int:
    return a * 10 ** num_digits(b) + b


def concat_product(n: int, k: int) -> int:
    acc = 0
    for i in range(k):
        acc = concat_nat(acc, n * (i + 1))
    return acc


def is_pandigital_1_to_9(n: int) -> bool:
    ds = digits_be(n)
    return len(ds) == 9 and all(1 <= d <= 9 for d in ds) and len(set(ds)) == 9


def naive(limit: int) -> int:
    vals = []
    for n in range(limit + 1):
        for k in range(9):
            if k + 1 > 1:
                v = concat_product(n, k + 1)
                if num_digits(v) == 9 and is_pandigital_1_to_9(v):
                    vals.append(v)
    return max(vals) if vals else 0


if __name__ == '__main__':
    assert concat_product(192, 3) == 192384576
    assert concat_product(9, 5) == 918273645

