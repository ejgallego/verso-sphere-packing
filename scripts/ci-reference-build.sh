#!/usr/bin/env bash

set -euo pipefail

scripts/ci-pre-build.sh
lake build +SpherePackingBlueprintMain 2>&1 | python3 scripts/filter_docstring_warnings.py --project-root .
