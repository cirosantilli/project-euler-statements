import itertools

from .common import of_digits_be


def naive(width: int = 9) -> int:
    """
    Split every permutation of the target digits into two positive factors and their product.

    @formalsw: Returns
    """
    if width < 3:
        return 0
    if width > 9:
        return 0
    products = set()
    pool = list(range(1, width + 1))
    for permutation in itertools.permutations(pool):
        digits = list(permutation)
        for first in range(1, width - 1):
            for second in range(first + 1, width):
                a = of_digits_be(digits[:first])
                b = of_digits_be(digits[first:second])
                product = of_digits_be(digits[second:])
                if a * b == product:
                    products.add(product)
    return sum(products)


def naive_default() -> int:
    return naive()
