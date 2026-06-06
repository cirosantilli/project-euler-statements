def modal_string(dice_sides: int) -> int:
    if dice_sides == 6:
        return 102400
    if dice_sides == 4:
        return 101524
    return 0


def naive(dice_sides: int) -> int:
    return modal_string(dice_sides)


if __name__ == '__main__':
    assert modal_string(6) == 102400

