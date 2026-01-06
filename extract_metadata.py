#!/usr/bin/env python3

import json
import os
import re
from os import path

TITLE_RE = re.compile(r"<title>(.*?)</title>", re.IGNORECASE | re.DOTALL)
PUBLISHED_RE = re.compile(r"Published on ([^;]+);")
DATE_RE = re.compile(
    r"^(?:(?:Monday|Tuesday|Wednesday|Thursday|Friday|Saturday|Sunday),\s*)?"
    r"(\d{1,2})(?:st|nd|rd|th)?\s+"
    r"([A-Za-z]+)\s+"
    r"(\d{4}),\s+"
    r"(\d{1,2}):(\d{2})\s*"
    r"([ap]m)$",
    re.IGNORECASE,
)

MONTHS = {
    "january": 1,
    "february": 2,
    "march": 3,
    "april": 4,
    "may": 5,
    "june": 6,
    "july": 7,
    "august": 8,
    "september": 9,
    "october": 10,
    "november": 11,
    "december": 12,
}


def extract_title(html):
    match = TITLE_RE.search(html)
    if not match:
        raise ValueError("No <title> element found")
    title = match.group(1).strip()
    title = re.sub(r"\s*-\s*Project Euler\s*$", "", title)
    title = re.sub(r"^#\d+\s+", "", title)
    return title


def parse_published_date(text):
    match = DATE_RE.match(text.strip())
    if not match:
        raise ValueError(f"Unrecognized published date: {text}")
    day = int(match.group(1))
    month_name = match.group(2).lower()
    year = int(match.group(3))
    hour = int(match.group(4))
    minute = int(match.group(5))
    ampm = match.group(6).lower()

    month = MONTHS.get(month_name)
    if not month:
        raise ValueError(f"Unknown month: {month_name}")

    if ampm == "am":
        hour = 0 if hour == 12 else hour
    else:
        hour = hour + 12 if hour < 12 else hour

    return f"{year:04d}-{month:02d}-{day:02d}T{hour:02d}:{minute:02d}:00"


def extract_published_iso(html):
    match = PUBLISHED_RE.search(html)
    if not match:
        raise ValueError("Published date not found")
    return parse_published_date(match.group(1))


def main():
    problem_dir = path.join("data", "problem")
    meta_dir = path.join("data", "meta")
    os.makedirs(meta_dir, exist_ok=True)

    for bname in sorted(os.listdir(problem_dir), key=lambda s: int(s.split(".")[0])):
        if not bname.endswith(".html"):
            continue
        bname_noext = path.splitext(bname)[0]
        html_path = path.join(problem_dir, bname)
        with open(html_path, "r") as html_f:
            html = html_f.read()

        meta = {
            "title": extract_title(html),
            "date": extract_published_iso(html),
        }

        meta_path = path.join(meta_dir, f"{bname_noext}.json")
        with open(meta_path, "w") as meta_f:
            json.dump(meta, meta_f, indent=2, ensure_ascii=True)
            meta_f.write("\n")


if __name__ == "__main__":
    main()
