#!/usr/bin/env python3
"""Check local Markdown links in the current documentation authorities."""

from __future__ import annotations

import re
import sys
from pathlib import Path
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parents[1]
CURRENT_DOCS = (
    Path("README.md"),
    Path("docs/README.md"),
    Path("docs/status.md"),
    Path("docs/roadmap.md"),
    Path("docs/dependencies.md"),
    Path("docs/point4/README.md"),
    Path("docs/palomar-submission-plan.md"),
    Path("docs/history/README.md"),
    Path("curvature/README.md"),
    Path("curvature/docs/curvature-package.md"),
)

LINK = re.compile(r"(?<!!)\[[^\]]*\]\(([^)\s]+)(?:\s+[^)]*)?\)")
SCHEME = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")


def local_target(source: Path, raw_target: str) -> Path | None:
    target = raw_target.strip("<>")
    if not target or target.startswith("#") or target.startswith("/"):
        return None
    if SCHEME.match(target):
        return None
    target = unquote(target.split("#", 1)[0].split("?", 1)[0])
    if not target:
        return None
    return (ROOT / source.parent / target).resolve()


def main() -> int:
    failures: list[str] = []
    checked = 0
    for source in CURRENT_DOCS:
        path = ROOT / source
        if not path.is_file():
            failures.append(f"{source}: documentation file is missing")
            continue
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            for match in LINK.finditer(line):
                target = local_target(source, match.group(1))
                if target is None:
                    continue
                checked += 1
                if not target.exists():
                    failures.append(
                        f"{source}:{line_number}: missing local target {match.group(1)}"
                    )

    if failures:
        print("Documentation link check failed:", file=sys.stderr)
        for failure in failures:
            print(f"- {failure}", file=sys.stderr)
        return 1

    print(f"Documentation link check passed ({checked} local links checked).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
