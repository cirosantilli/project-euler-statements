def xor(a: int, b: int) -> int:
    """
    @formalsw: Returns
    """
    return a ^ b


def decrypt(cipher: bytes, key: list[int]) -> list[int]:
    return [xor(c, key[i % len(key)] if key else 0) for i, c in enumerate(cipher)]


def char_weight(value: int) -> int:
    """
    @formalsw: Requires(value >= 0)
    @formalsw: Requires(value < 256)
    @formalsw: Returns
    """
    if 65 <= value <= 90:
        value += 32
    if value == 32:
        return 10
    if value == 101:
        return 6
    if value in b"tao":
        return 5
    if value in b"inshr":
        return 4
    if value in b"dl":
        return 3
    if value in b"ucmwfgyp":
        return 2
    if value in b"bvk.,;:'\"!?()-":
        return 1
    if value in b"{}[]|^~`":
        return -3
    return 0


def text_score(text: list[int]) -> int | None:
    score = 0
    for value in text:
        if not (32 <= value <= 126 or value == 10 or value == 13):
            return None
        score += char_weight(value)
    return score


def keys() -> list[list[int]]:
    letters = list(range(97, 123))
    return [[a, b, c] for a in letters for b in letters for c in letters]


def naive(cipher: bytes) -> int:
    # Materialize and score every decryption, retaining the first key on ties.
    best_score: int | None = None
    best_sum = 0
    for k in keys():
        text = decrypt(cipher, k)
        score = text_score(text)
        if score is not None and (best_score is None or score > best_score):
            best_score = score
            best_sum = sum(text)
    return best_sum


if __name__ == '__main__':
    assert xor(65, 42) == 107
    assert decrypt(bytes([65]), [42]) == [107]
    assert char_weight(69) == char_weight(101) == 6
    assert char_weight(39) == 1
    assert text_score([65, 10, 13]) == 5
    assert text_score([0]) is None
    assert naive(b'') == 0
    assert naive(bytes([0])) == 101
    assert naive(bytes([0, 255])) == 0

