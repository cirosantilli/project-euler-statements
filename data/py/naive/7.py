from common import is_prime


def naive(n: int) -> int:
    if n == 0:
        return 0
    count = 0
    x = 1
    while count < n:
        x += 1
        if is_prime(x):
            count += 1
    return x


if __name__ == '__main__':
    assert naive(6) == 13
