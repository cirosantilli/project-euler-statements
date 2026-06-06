def word_value(s: str) -> int:
    return sum(ord(c) - ord('A') + 1 for c in s)


def is_triangle(n: int) -> bool:
    return any(k * (k + 1) // 2 == n for k in range(n + 1))


def naive(words: list[str]) -> int:
    return sum(1 for w in words if is_triangle(word_value(w)))


if __name__ == '__main__':
    assert word_value('SKY') == 55
    assert is_triangle(55)

