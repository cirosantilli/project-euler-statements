from common import digits_be, of_digits_be


def naive(nums: list[int], k: int) -> int:
    return of_digits_be(digits_be(sum(nums))[:k])

