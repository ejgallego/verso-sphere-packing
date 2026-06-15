#!/usr/bin/env bash

set -euo pipefail

python3 scripts/disable_slow_header_linter.py
lake build +SpherePackingBlueprintMain 2>&1 | python3 scripts/filter_docstring_warnings.py --project-root .
