from .common import digits_be


def champernowne_digits(limit: int) -> list[int]:
    out = []
    for i in range(limit):
        out += digits_be(i + 1)
    return out


def digit_at(n: int) -> int:
    """
    Extend the decimal stream until the requested one-based position exists.
    """
    if n < 1:
        raise ValueError("Position must be positive")
    digits = []
    value = 1
    while len(digits) < n:
        digits.extend(digits_be(value))
        value += 1
    return digits[n - 1]


def naive(positions: tuple[int, ...] = (1, 10, 100, 1000, 10000, 100000, 1000000)) -> int:
    product = 1
    for position in positions:
        product *= digit_at(position)
    return product


def naive_default() -> int:
    return naive()


if __name__ == '__main__':
    assert digit_at(12) == 1

