# AGENTS

Repository-specific guidance for Codex agents working in this tree.

## Upstream Reference Tree

- `Sphere-Packing-LaTeX-Reference/` is the upstream formalization checkout for this repo.
- Keep it as a read-only submodule and the authoritative Lake dependency for the `SpherePacking` package.
- Do not copy `SpherePacking` modules into the host root when the path dependency can be used directly.

## Bringing Upstream Lean Code In

- Prefer using the upstream `SpherePacking` package through the path dependency in `lakefile.lean`.
- If a local compatibility layer is needed for blueprint imports, keep it in `SpherePackingBlueprint/ToolchainWorkarounds.lean`.
- Only copy upstream Lean sources into the host root if the user explicitly asks for a temporary fork away from the canonical harness.

## Toolchain Policy

- The repo root `lean-toolchain` must match `Sphere-Packing-LaTeX-Reference/lean-toolchain` exactly.
- Do not bump the consumer toolchain independently; update the upstream formalization first and then copy that value to the root.
- If an upstream proof later needs repair after an upstream toolchain move and the repair is not easy, comment the issue very clearly at the failure site and leave a `sorry` with a short explanation.
- Favor using real upstream declarations, even if they currently contain `sorry`, over inventing coarse placeholder declarations.

## Dependency / Manifest Discipline

- Keep the main repo as a single package unless the user explicitly asks otherwise.
- Avoid unnecessary `lake update` runs because they can rewrite `lake-manifest.json` and drift pinned dependency revisions.

## Build Hygiene

- Before expensive Lean builds, run the mathlib cache fetch command.
- Prefer `nice` for `lake build` so the machine stays usable during long compiles.
- Concretely, prefer `nice -n 10 lake exe cache get` before large builds, and `nice -n 10 lake build ...` for the build itself.
- Avoid running multiple `lake build` jobs in parallel in this repo, because they can race on generated build artifacts.

## Leanblueprint To Verso Harness Notes

- This repo uses the local helper at `tools/verso-harness`.
- Keep a root `verso-harness.toml` checked in and treat it as the source of
  truth for package layout, LT chapter scope, and the TeX source path.
- Before porting or maintaining blueprint files, read:
  - `tools/verso-harness/references/layout.md`
  - `tools/verso-harness/references/lt-method.md`
  - `tools/verso-harness/references/porting.md`
  - `tools/verso-harness/references/maintenance.md`
  - `tools/verso-harness/references/retrofit.md`
  - `tools/verso-harness/references/beam-validation.md`
- Use `python3 tools/verso-harness/scripts/check_harness.py --project-root .`
  to audit the local harness.
- Treat the legacy TeX or `leanblueprint` source as the prose source of truth.
- Record the real TeX chapter source path for this repo. The common legacy
  layout is `./blueprint/src/chapter/*.tex`, but verify it before wiring status
  pages or source-backed notes.
- The default deliverable for direct-port chapters is an LT pass. Do not trust
  older LT labels by themselves; every translated informal block now needs an
  adjacent local `tex` witness.
- Preserve section order, paragraph boundaries, labeled theorem order, and
  important dependency edges when translating to Verso.
- Treat the host formalization as the source of truth.
- Prefer `(lean := "...")` links to real declarations rather than duplicating
  Lean code in blueprint modules.
- Preserve TeX `\uses{...}` edges as Verso `{uses "..."}[]` references inside
  the relevant node or proof, not just in free prose.
- When a standalone line would otherwise consist only of consecutive
  `{uses "..."}[]` references, rewrite it deterministically as a sentence that
  starts with `Uses`.
- Use exactly `Uses {uses "..."}[].` for one edge, `Uses {uses "..."}[] and
  {uses "..."}[].` for two edges, and `Uses {uses "..."}[], {uses "..."}[],
  and {uses "..."}[].` for three or more edges.
- Do not paraphrase, reorder, or integrate those standalone `Uses ...` lines
  into surrounding prose; this is a presentation-only normalization that
  applies equally to statements and proofs.
- When the source block still needs to stay visible, prefer a labeled local
  `tex` block over rewriting it into placeholder prose.
- Treat metadata cleanup as a second phase of LT rather than as a substitute
  for LT.
- Port coherent chapter blocks rather than scattering small edits across
  unrelated chapters.
- Keep shared TeX macros in one `TeXPrelude.lean` module.
- Prefer the harness pattern where `VersoBlueprint` drives the `verso`
  dependency unless this repo has a concrete reason to pin `verso` directly.
- After editing direct-port chapters, run:
  - `python3 tools/verso-harness/scripts/check_lt_source_pairs.py --project-root . <chapter.lean>`
  - `python3 tools/verso-harness/scripts/check_lt_similarity.py --project-root . <chapter.lean>`
- Use `python3 tools/verso-harness/scripts/check_source_label_grounding.py --project-root . <chapter.lean>`
- Use `python3 tools/verso-harness/scripts/lt_audit.py --project-root . <chapter.lean>`
  when you want the source-pair check, similarity report, focused build, and
  optional pages smoke test in one command.
- After a coherent batch, run `bash ./scripts/ci-pages.sh`.
- Keep the root build green. If a Lean link would pull in imports that are not
  harness-clean on the current toolchain, leave the node informal and note the
  dependency in prose instead.
- If using `lean-beam`, avoid parallel `sync` calls against the same project
  root unless the target repo is known to tolerate it.
