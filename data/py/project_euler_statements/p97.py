def mod_pow(a: int, b: int, m: int) -> int:
    acc = 1
    a %= m
    for _ in range(b):
        acc = acc * a % m
    return acc


def naive() -> int:
    m = 10 ** 10
    return (28433 * mod_pow(2, 7830457, m) + 1) % m

