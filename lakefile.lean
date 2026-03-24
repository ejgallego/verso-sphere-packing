import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso"@"main"
require VersoBlueprint from git "https://github.com/ejgallego/verso-blueprint"@"0c236007b9e702a188af84a2dc4f3725e778e2af"
package VersoSpherePacking where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib SpherePackingBlueprint where
  roots := #[`SpherePackingBlueprint]

@[default_target]
lean_exe «blueprint-gen» where
  root := `SpherePackingBlueprintMain
  supportInterpreter := true
