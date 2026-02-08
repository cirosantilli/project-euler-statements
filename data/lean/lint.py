#!/usr/bin/env python3
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
IMPORTS_FILE = ROOT / "ProjectEulerStatements.lean"
PROBLEMS_DIR = ROOT / "ProjectEulerStatements"

IMPORT_RE = re.compile(r"^import\s+ProjectEulerStatements\.P(\d+)$")


def main() -> int:
    if not IMPORTS_FILE.exists():
        print(f"missing {IMPORTS_FILE}")
        return 2

    text = IMPORTS_FILE.read_text(encoding="utf-8")
    imported_nums = []
    for line in text.splitlines():
        m = IMPORT_RE.match(line.strip())
        if m:
            imported_nums.append(int(m.group(1)))

    if not imported_nums:
        print("no ProjectEulerStatements.P* imports found")
        return 2

    last = max(imported_nums)

    missing = [n for n in range(1, last + 1) if n not in imported_nums]
    if missing:
        print("missing imports:")
        for n in missing:
            print(f"  ProjectEulerStatements.P{n}")
        return 1

    print(f"ok: all ProjectEulerStatements.P1..P{last} are imported")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
