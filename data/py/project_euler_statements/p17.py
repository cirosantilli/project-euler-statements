def small_word_len(n: int) -> int:
    return {0:0,1:3,2:3,3:5,4:4,5:4,6:3,7:5,8:5,9:4,10:3,11:6,12:6,13:8,14:8,15:7,16:7,17:9,18:8,19:8}.get(n, 0)


def tens_word_len(n: int) -> int:
    return {2:6,3:6,4:5,5:5,6:5,7:7,8:6,9:6}.get(n, 0)


def word_len(n: int) -> int:
    if n == 0:
        return 0
    if n < 20:
        return small_word_len(n)
    if n < 100:
        return tens_word_len(n // 10) + small_word_len(n % 10)
    if n < 1000:
        h, r = divmod(n, 100)
        return small_word_len(h) + 7 + (0 if r == 0 else 3 + word_len(r))
    if n == 1000:
        return 3 + 8
    return 0


def naive(n: int) -> int:
    return sum(word_len(i) for i in range(n + 1))


if __name__ == '__main__':
    assert naive(5) == 19
    assert word_len(342) == 23
    assert word_len(115) == 20

