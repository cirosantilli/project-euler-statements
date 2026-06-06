def sum_unique(xs: list[int]) -> int:
    seen = []
    for x in xs:
        if x not in seen:
            seen.append(x)
    return sum(seen)


def dfs(start, prod, summ, terms, k_max, limit, best):
    max_f = limit // prod
    f = start
    while f <= max_f:
        new_prod = prod * f
        new_sum = summ + f
        new_terms = terms + 1
        k = new_terms + (new_prod - new_sum)
        if k <= k_max and new_prod < best[k]:
            best[k] = new_prod
        if k <= k_max:
            dfs(f, new_prod, new_sum, new_terms, k_max, limit, best)
        f += 1
    return best


def naive(k_max: int) -> int:
    limit = 2 * k_max
    best = [10 ** 18] * (k_max + 1)
    dfs(2, 1, 0, 0, k_max, limit, best)
    seen = [False] * (limit + 1)
    total = 0
    for k in range(2, k_max + 1):
        v = best[k]
        if v <= limit and not seen[v]:
            seen[v] = True
            total += v
    return total


if __name__ == '__main__':
    assert sum_unique([4, 6, 8, 12]) == 30
    assert sum_unique([4, 6, 8, 12, 15, 16]) == 61
    assert naive(6) == 30
    assert naive(12) == 61

