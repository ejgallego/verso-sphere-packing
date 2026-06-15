#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path


FORMALIZATION_LAKEFILE = Path("Sphere-Packing-LaTeX-Reference/lakefile.toml")
MATHLIB_STANDARD_SET = "weak.linter.mathlibStandardSet = true\n"
HEADER_OVERRIDE = "weak.linter.style.header = false\n"


def main() -> int:
    if not FORMALIZATION_LAKEFILE.exists():
        raise SystemExit(f"missing formalization lakefile: {FORMALIZATION_LAKEFILE}")

    text = FORMALIZATION_LAKEFILE.read_text(encoding="utf-8")
    if HEADER_OVERRIDE in text:
        print(f"[ci-linters] header linter already disabled in {FORMALIZATION_LAKEFILE}")
        return 0

    if MATHLIB_STANDARD_SET not in text:
        raise SystemExit(
            f"expected {FORMALIZATION_LAKEFILE} to enable weak.linter.mathlibStandardSet"
        )

    FORMALIZATION_LAKEFILE.write_text(
        text.replace(MATHLIB_STANDARD_SET, MATHLIB_STANDARD_SET + HEADER_OVERRIDE, 1),
        encoding="utf-8",
    )
    print(f"[ci-linters] disabled slow header linter in {FORMALIZATION_LAKEFILE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
