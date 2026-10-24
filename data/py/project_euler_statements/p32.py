from .common import digits_be


def is_pandigital_1_to_9(ds: list[int]) -> bool:
    """
    @formalsw: Returns
    """
    return len(ds) == 9 and all(1 <= d <= 9 for d in ds) and len(set(ds)) == 9


def pandigital_product(a: int, b: int) -> bool:
    """
    @formalsw: Requires(a >= 0 and b >= 0)
    @formalsw: Returns
    """
    return is_pandigital_1_to_9(digits_be(a) + digits_be(b) + digits_be(a * b))


def naive(max_a: int, max_b: int) -> int:
    """
    @formalsw: Returns
    """
    products = [a * b for a in range(max_a + 1) for b in range(max_b + 1) if a and b and pandigital_product(a, b)]
    return sum(set(products))


def naive_default() -> int:
    """
    @formalsw: Returns
    """
    return naive(99, 9999)


if __name__ == '__main__':
    assert pandigital_product(39, 186)

