from common import proper_divisor_sum


def chain(start: int, limit: int) -> list[int]:
    x, seen = start, []
    for _ in range(limit + 1):
        if x == 0 or x > limit:
            return []
        if x in seen:
            return list(reversed(seen)) if x == start else []
        seen.insert(0, x)
        x = proper_divisor_sum(x)
    return []


def longest_chain(limit: int) -> list[int]:
    best = []
    for n in range(limit + 1):
        c = chain(n, limit)
        if len(c) > len(best):
            best = c
    return best


def naive(limit: int) -> int:
    c = longest_chain(limit)
    return min(c) if c else 0


if __name__ == '__main__':
    assert proper_divisor_sum(28) == 28

