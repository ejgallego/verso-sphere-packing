import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso"@"main"
require VersoBlueprint from git "https://github.com/ejgallego/verso-blueprint"@"main"

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
