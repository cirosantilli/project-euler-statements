from .common import digits_be


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


def naive() -> int:
    """
    Two or more products must fit in nine digits, so the base has at most four digits.
    """
    best = 0
    digits = 9
    for n in range(1, 10 ** (digits // 2)):
        k = 1
        while num_digits(concat_product(n, k)) <= digits:
            value = concat_product(n, k)
            if k > 1 and is_pandigital_1_to_9(value):
                best = max(best, value)
            k += 1
    return best


def naive_default() -> int:
    return naive()


if __name__ == '__main__':
    assert concat_product(192, 3) == 192384576
    assert concat_product(9, 5) == 918273645

