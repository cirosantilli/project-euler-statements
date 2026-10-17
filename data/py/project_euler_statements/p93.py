from itertools import combinations, permutations


def eval_ops(a: int, b: int) -> list[int]:
    out = [a + b, a - b, b - a, a * b]
    if b != 0:
        out.append(a // b)
    if a != 0:
        out.append(b // a)
    return out


def all_results(nums: list[int]) -> list[int]:
    if not nums:
        return []
    if len(nums) == 1:
        return nums[:]
    a, b, *tl = nums
    out = []
    for v in eval_ops(a, b):
        out += all_results([v] + tl)
    return out


def positive_ints(xs):
    return [x for x in xs if x > 0]


def consecutive_count(xs):
    s = set(xs)
    n = 1
    for _ in range(len(s) + 2):
        if n in s:
            n += 1
        else:
            return n - 1
    return n - 1


def consecutive_for_digits(digits: list[int]) -> int:
    results = []
    for p in permutations(digits):
        results += all_results(list(p))
    return consecutive_count(positive_ints(results))


def digits_to_nat(digits: list[int]) -> int:
    acc = 0
    for d in digits:
        acc = acc * 10 + d
    return acc


def naive() -> int:
    best_len, best_digits = 0, []
    for digits in combinations(range(10), 4):
        l = consecutive_for_digits(list(digits))
        if l > best_len:
            best_len, best_digits = l, list(digits)
    return digits_to_nat(best_digits)


if __name__ == '__main__':
    assert consecutive_for_digits([1, 2, 3, 4]) == 28

