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


def naive() -> int:
    """
    Split every permutation of the problem's nine digits into two factors and a product.
    """
    from itertools import permutations

    products = set()
    for digits in permutations("123456789"):
        text = "".join(digits)
        for first in range(1, len(text) - 1):
            for second in range(first + 1, len(text)):
                product = int(text[second:])
                if int(text[:first]) * int(text[first:second]) == product:
                    products.add(product)
    return sum(products)


def naive_default() -> int:
    return naive()


if __name__ == '__main__':
    assert pandigital_product(39, 186)

