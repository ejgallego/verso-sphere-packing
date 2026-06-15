#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path


FORMALIZATION_LAKEFILE = Path("Sphere-Packing-LaTeX-Reference/lakefile.toml")
MATHLIB_STANDARD_SET_ENABLED = "weak.linter.mathlibStandardSet = true\n"
MATHLIB_STANDARD_SET_DISABLED = "weak.linter.mathlibStandardSet = false\n"
HEADER_DISABLED = "weak.linter.style.header = false\n"


def main() -> int:
    if not FORMALIZATION_LAKEFILE.exists():
        raise SystemExit(f"missing formalization lakefile: {FORMALIZATION_LAKEFILE}")

    text = FORMALIZATION_LAKEFILE.read_text(encoding="utf-8")
    if MATHLIB_STANDARD_SET_DISABLED in text and HEADER_DISABLED in text:
        print(f"[ci-linters] slow mathlib linter set already disabled in {FORMALIZATION_LAKEFILE}")
        return 0

    if MATHLIB_STANDARD_SET_ENABLED not in text:
        raise SystemExit(
            f"expected {FORMALIZATION_LAKEFILE} to enable weak.linter.mathlibStandardSet"
        )

    replacement = MATHLIB_STANDARD_SET_DISABLED
    if HEADER_DISABLED not in text:
        replacement += HEADER_DISABLED

    FORMALIZATION_LAKEFILE.write_text(
        text.replace(MATHLIB_STANDARD_SET_ENABLED, replacement, 1),
        encoding="utf-8",
    )
    print(f"[ci-linters] disabled slow mathlib linter set in {FORMALIZATION_LAKEFILE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
