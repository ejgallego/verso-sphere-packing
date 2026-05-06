# Verso Sphere Packing

[![Blueprint Pages](https://github.com/ejgallego/verso-sphere-packing/actions/workflows/blueprint.yml/badge.svg)](https://github.com/ejgallego/verso-sphere-packing/actions/workflows/blueprint.yml)

Verso Blueprint port of the Sphere Packing Blueprint, with the upstream
[`Sphere-Packing-Lean`](Sphere-Packing-LaTeX-Reference/) formalization carried
locally as a submodule.

Blueprint: <https://ejgallego.github.io/verso-sphere-packing/>

This repo follows the upstream blueprint strictly and translates its source
markup language to Verso with the help of AI.

## Build

```bash
lake build
```

## Generate

```bash
lake env lean --run SpherePackingBlueprintMain.lean --output _out/site
```

This repository follows the shared
[`tools/verso-harness`](tools/verso-harness/) workflow. The root
[`lean-toolchain`](lean-toolchain) matches the upstream formalization, and
[`lakefile.lean`](lakefile.lean) pins `VersoBlueprint` to the matching release
branch.
