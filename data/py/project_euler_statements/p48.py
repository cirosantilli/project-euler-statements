def mod_pow(a: int, b: int, m: int) -> int:
    """
    @formalsw: Requires(m != 0)
    @formalsw: Returns
    """
    acc = 1
    a %= m
    for _ in range(b):
        acc = acc * a % m
    return acc


def series_mod(n: int, m: int) -> int:
    """
    @formalsw: Requires(m != 0)
    @formalsw: Returns
    """
    acc = 0
    for i in range(n):
        acc = (acc + mod_pow(i + 1, i + 1, m)) % m
    return acc


def naive(n: int) -> int:
    """
    @formalsw: Returns
    """
    return series_mod(n, 10 ** 10)


def naive_digits(n: int, k: int = 10) -> str:
    """
    Format the original repeated-multiplication series at a chosen decimal width.

    @formalsw: Requires(k >= 0)
    @formalsw: Returns
    """
    return str(series_mod(n, 10 ** k)).zfill(k)


if __name__ == '__main__':
    assert series_mod(10, 10 ** 10) == 10405071317 % (10 ** 10)

