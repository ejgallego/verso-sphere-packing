# Verso Sphere Packing

[![Blueprint Pages](https://github.com/ejgallego/verso-sphere-packing/actions/workflows/pages.yml/badge.svg)](https://github.com/ejgallego/verso-sphere-packing/actions/workflows/pages.yml)

Standalone Verso Blueprint example project for the Sphere Packing in Lean
document.

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

This repository keeps its committed `VersoBlueprint` dependency pointed at the
official upstream package. Local maintainers can override that dependency
ephemerally during testing.
