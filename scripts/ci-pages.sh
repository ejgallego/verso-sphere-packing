#!/usr/bin/env bash

set -euo pipefail

step() {
  printf '\n[ci-pages] %s\n' "$*" >&2
}

step "disabling slow header linter"
python3 scripts/disable_slow_header_linter.py

step "warming dependency cache"
python3 tools/verso-harness/scripts/ensure_dependency_cache.py --project-root . --warm-cache

step "building SpherePackingBlueprintMain"
lake build +SpherePackingBlueprintMain 2>&1 | python3 scripts/filter_docstring_warnings.py --project-root .

step "checking dependency cache after build"
python3 tools/verso-harness/scripts/ensure_dependency_cache.py --project-root .

step "generating site"
lake env lean --run SpherePackingBlueprintMain.lean --output _out/site 2>&1 | python3 scripts/filter_docstring_warnings.py --project-root .

step "checking generated site"
python3 tools/verso-harness/scripts/check_generated_site.py --project-root . --site-dir _out/site/html-multi
