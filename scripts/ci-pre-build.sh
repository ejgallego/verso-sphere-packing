#!/usr/bin/env bash

set -euo pipefail

# Upstream owns its Lake options. Consumer builds must leave it unchanged.
git -C Sphere-Packing-LaTeX-Reference diff --exit-code HEAD -- .
