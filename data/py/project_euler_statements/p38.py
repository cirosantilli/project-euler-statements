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


def is_pandigital(n: int, width: int = 9) -> bool:
    ds = digits_be(n)
    return len(ds) == width and all(1 <= d <= width for d in ds) and len(set(ds)) == width


def naive(width: int = 9) -> int:
    """
    @formalsw: Returns
    """
    if width < 2:
        return 0
    if width > 9:
        return 0
    vals = []
    for n in range(1, 10 ** (width // 2)):
        for k in range(2, width + 1):
            value = concat_product(n, k)
            if is_pandigital(value, width):
                vals.append(value)
    return max(vals) if vals else 0


def naive_default() -> int:
    return naive()


if __name__ == '__main__':
    assert concat_product(192, 3) == 192384576
    assert concat_product(9, 5) == 918273645
