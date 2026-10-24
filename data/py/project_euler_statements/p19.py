from dataclasses import dataclass


def is_leap(y: int) -> bool:
    """
    @formalsw: Returns
    """
    return y % 4 == 0 and (y % 100 != 0 or y % 400 == 0)


def days_in_month(y: int, m: int) -> int:
    return [0,31,29 if is_leap(y) else 28,31,30,31,30,31,31,30,31,30,31][m] if 1 <= m <= 12 else 0


@dataclass(frozen=True)
class Date:
    year: int
    month: int
    day: int


def days_in_year(y: int) -> int:
    return 366 if is_leap(y) else 365


def days_before_year(y: int) -> int:
    return sum(days_in_year(1900 + i) for i in range(y - 1900))


def days_before_month(y: int, m: int) -> int:
    return sum(days_in_month(y, i + 1) for i in range(m - 1))


def day_of_week(y: int, m: int, d: int) -> int:
    return (days_before_year(y) + days_before_month(y, m) + (d - 1)) % 7


def date_to_days(d: Date) -> int:
    """
    @formalsw: Returns
    """
    return days_before_year(d.year) + days_before_month(d.year, d.month) + (d.day - 1)


def count_sundays_between(start_date: Date, end_date: Date) -> int:
    start_days = date_to_days(start_date)
    end_days = date_to_days(end_date)
    acc = 0
    for y in range(start_date.year, end_date.year + 1):
        for m in range(1, 13):
            days = days_before_year(y) + days_before_month(y, m)
            if start_days <= days <= end_days and day_of_week(y, m, 1) == 6:
                acc += 1
    return acc


def naive(start_date: Date, end_date: Date) -> int:
    """
    @formalsw: Returns
    """
    return count_sundays_between(start_date, end_date)


def naive_years(start_year: int, end_year: int) -> int:
    """
    Count first-of-month Sundays from January through December, inclusive.
    @formalsw: Returns
    """
    return naive(Date(start_year, 1, 1), Date(end_year, 12, 31))


if __name__ == '__main__':
    assert day_of_week(1900, 1, 1) == 0

