def value(c: str) -> int:
    return {'I':1,'V':5,'X':10,'L':50,'C':100,'D':500,'M':1000}.get(c, 0)


def roman_to_int(chars: list[str]) -> int:
    if not chars:
        return 0
    if len(chars) == 1:
        return value(chars[0])
    a, b = chars[0], chars[1]
    if value(a) < value(b):
        return value(b) - value(a) + roman_to_int(chars[2:])
    return value(a) + roman_to_int(chars[1:])


def int_to_roman_aux(n: int) -> list[str]:
    table = [(1000,['M']),(900,['C','M']),(500,['D']),(400,['C','D']),(100,['C']),(90,['X','C']),(50,['L']),(40,['X','L']),(10,['X']),(9,['I','X']),(5,['V']),(4,['I','V']),(1,['I'])]
    out = []
    for v, cs in table:
        while n >= v:
            out += cs
            n -= v
    return out


def minimal_roman(s: str) -> str:
    return ''.join(int_to_roman_aux(roman_to_int(list(s))))


def saved_chars(s: str) -> int:
    return len(s) - len(minimal_roman(s))


def naive(list_: list[str]) -> int:
    return sum(saved_chars(s) for s in list_)


if __name__ == '__main__':
    assert roman_to_int(list('XVI')) == 16

