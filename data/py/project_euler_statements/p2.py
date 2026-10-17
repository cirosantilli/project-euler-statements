#!/usr/bin/env python

def naive(n: int) -> int:
    """
    @formalsw: Requires(n >= 0)
    @formalsw: Returns
    """
    total = 0
    a = 1
    b = 2
    while True:
        if b > n:
            return total
        if b % 2 == 0:
            total += b
        a, b = b, a + b
