#!/usr/bin/env python3
from pathlib import Path
import re

root = Path.cwd()
paths = []
if (root / "FloorSaving").exists():
    paths.extend((root / "FloorSaving").glob("**/*.lean"))
if (root / "FloorSaving.lean").exists():
    paths.append(root / "FloorSaving.lean")

pattern = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")

print("# Current placeholder scan")
for path in sorted(paths):
    rel = path.relative_to(root)
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if pattern.search(line):
            print(f"{rel}:{i}: {line.strip()}")
