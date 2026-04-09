# Verso Sphere Packing

[![Blueprint Pages](https://github.com/ejgallego/verso-sphere-packing/actions/workflows/blueprint.yml/badge.svg)](https://github.com/ejgallego/verso-sphere-packing/actions/workflows/blueprint.yml)

Verso blueprint harness for the Sphere Packing in Lean document, with the
upstream `Sphere-Packing-Lean` formalization carried locally as a submodule.

Published site on `main`: <https://ejgallego.github.io/verso-sphere-packing/>
(after the first successful GitHub Pages deployment).

## Build

```bash
lake build
```

## Generate

```bash
lake exe blueprint-gen
```

## CI / Pages

```bash
./scripts/ci-pages.sh
```

This matches the included GitHub Actions Pages workflow and checks the rendered
site entry point plus the shared preview manifest under `_out/site/html-multi`.

This repository follows the shared `tools/verso-harness` workflow. The root
`lean-toolchain` matches the upstream `Sphere-Packing-Lean` formalization, and
`VersoBlueprint` is pinned to the matching `lean-v4.28.0` branch.
