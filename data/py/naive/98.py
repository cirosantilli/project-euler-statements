from common import digits_le


def digits_sorted(n: int) -> list[int]:
    return sorted(digits_le(n))


def anagrams(words: list[str]) -> list[tuple[str, str]]:
    out = []
    for i, w in enumerate(words):
        key = sorted(w)
        for u in words[i + 1:]:
            if w != u and key == sorted(u):
                out.append((w, u))
    return out


def naive(words: list[str]) -> int:
    return len(anagrams(words))


if __name__ == '__main__':
    assert digits_sorted(1296) == digits_sorted(9216)

