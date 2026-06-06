#!/usr/bin/env python3
from __future__ import annotations

import shutil
import subprocess
from pathlib import Path


def problem_number(path: Path) -> int:
    return int(path.stem)


def main() -> int:
    root = Path(__file__).resolve().parent
    naive_dir = root / 'naive'
    files = sorted(
        (p for p in naive_dir.glob('*.py') if p.stem.isdigit()),
        key=problem_number,
    )
    exe = shutil.which('pypy') or shutil.which('pypy3')
    if exe is None:
        print('ERROR: neither pypy nor pypy3 was found on PATH')
        return 127
    failed = []
    for path in files:
        rel = path.relative_to(root)
        print(f'RUN {rel}')
        proc = subprocess.run([exe, str(path.resolve())], cwd=naive_dir)
        if proc.returncode != 0:
            failed.append((path.name, proc.returncode))
    if failed:
        print('FAILED:')
        for name, code in failed:
            print(f'  {name}: exit {code}')
        return 1
    print(f'OK: {len(files)} files')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
