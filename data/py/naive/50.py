from common import is_prime


def primes_below(limit: int) -> list[int]:
    return [n for n in range(limit) if is_prime(n)]


def prefix_sums(xs: list[int]) -> list[int]:
    acc = []
    for x in xs:
        acc.append(x + (acc[-1] if acc else 0))
    return acc


def sum_range(pref: list[int], i: int, j: int) -> int:
    if i == 0:
        return pref[j - 1] if 0 <= j - 1 < len(pref) else 0
    return (pref[j - 1] if 0 <= j - 1 < len(pref) else 0) - (pref[i - 1] if 0 <= i - 1 < len(pref) else 0)


def naive(limit: int) -> int:
    ps = primes_below(limit)
    pref = prefix_sums(ps)
    candidates = []
    for i in range(len(ps) + 1):
        for j in range(len(ps) + 1):
            if i < j:
                s = sum_range(pref, i, j)
                if s < limit and is_prime(s):
                    candidates.append((j - i, s))
    return max(candidates, key=lambda p: p[0])[1] if candidates else 0


if __name__ == '__main__':
    assert 41 == 2 + 3 + 5 + 7 + 11 + 13
    assert sum_range(prefix_sums(primes_below(100)), 0, 6) == 41
    assert sum_range(prefix_sums(primes_below(1000)), 3, 24) == 953

