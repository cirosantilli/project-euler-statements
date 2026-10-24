from .common import digits_be


def digit_at(n: int) -> int:
    """
    Extend the decimal stream until the requested one-based position exists.
    """
    if n < 1:
        raise ValueError("Position must be positive")
    digits = []
    value = 1
    while len(digits) < n:
        digits += digits_be(value)
        value += 1
    return digits[n - 1]


def naive(positions: tuple[int, ...]) -> int:
    product = 1
    for position in positions:
        product *= digit_at(position)
    return product


if __name__ == '__main__':
    assert digit_at(12) == 1

