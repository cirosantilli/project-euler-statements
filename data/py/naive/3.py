#!/usr/bin/env python

from common import is_prime


def naive(n: int) -> int:
    for k in range(n, 1, -1):
        if n % k == 0 and is_prime(k)
            return k
    return 0


if __name__ == '__main__':
    assert naive(13195) == 29

