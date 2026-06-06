def naive(n: int) -> int:
    if n == 0:
        return 0
    m = n - 1
    s = naive(m)
    return s + m if m % 3 == 0 or m % 5 == 0 else s


def naive2(max_: int) -> int:
    return sum(x for x in range(max_) if x % 3 == 0 or x % 5 == 0)


if __name__ == '__main__':
    assert naive(10) == 23

