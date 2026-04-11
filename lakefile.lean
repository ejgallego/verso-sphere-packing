import Lake
open Lake DSL

require SpherePacking from "./Sphere-Packing-LaTeX-Reference"
require VersoBlueprint from git "https://github.com/ejgallego/verso-blueprint.git" @ "v4.28.0"

package SpherePackingBlueprint where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.hashCommand, false⟩,
    ⟨`weak.verso.blueprint.math.lint, true⟩,
    ⟨`weak.verso.blueprint.externalCode.strictResolve, true⟩,
    ⟨`verso.code.warnLineLength, .ofNat 0⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩
  ]

@[default_target]
lean_lib SpherePackingBlueprint where
  roots := #[`SpherePackingBlueprint]

@[default_target]
lean_exe «blueprint-gen» where
  root := `SpherePackingBlueprintMain
  supportInterpreter := true
