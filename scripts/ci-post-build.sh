#!/usr/bin/env bash

set -euo pipefail

# Catch source or configuration rewrites introduced by cache warming/builds.
git -C Sphere-Packing-LaTeX-Reference diff --exit-code HEAD -- .
