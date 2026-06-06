def letter_value(c: str) -> int:
    n = ord(c)
    a = ord('A')
    return n - a + 1 if a <= n <= ord('Z') else 0


def name_value(s: str) -> int:
    return sum(letter_value(c) for c in s)


def name_score(pos: int, name: str) -> int:
    return pos * name_value(name)


def naive(names: list[str]) -> int:
    return sum(name_score(i, name) for i, name in enumerate(sorted(names), 1))


if __name__ == '__main__':
    assert name_value('COLIN') == 53
    assert name_score(938, 'COLIN') == 49714

