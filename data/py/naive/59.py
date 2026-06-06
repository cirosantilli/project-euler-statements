def xor(a: int, b: int) -> int:
    return a ^ b


def decrypt(cipher: list[int], key: list[int]) -> list[int]:
    return [xor(c, key[i % len(key)] if key else 0) for i, c in enumerate(cipher)]


def contains_sublist(text: list[int], pattern: list[int]) -> bool:
    if pattern == []:
        return True
    return any(text[i:i + len(pattern)] == pattern for i in range(len(text) + 1))


def looks_english(text: list[int]) -> bool:
    return contains_sublist(text, [116, 104, 101])


def keys() -> list[list[int]]:
    letters = list(range(97, 123))
    return [[a, b, c] for a in letters for b in letters for c in letters]


def naive(cipher: list[int]) -> int:
    for k in keys():
        text = decrypt(cipher, k)
        if looks_english(text):
            return sum(text)
    return 0

