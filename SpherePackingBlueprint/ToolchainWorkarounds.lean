import SpherePacking
import SpherePackingBlueprint.Macros

set_option autoImplicit false

/-
Compatibility import shim for the blueprint chapters.

The chapters still import `SpherePackingBlueprint.ToolchainWorkarounds`, but the
module now just re-exports the upstream `SpherePacking` package from the local
`Sphere-Packing-LaTeX-Reference` path dependency. If a future toolchain mismatch
forces local temporary patches, keep them here and prefer real upstream
declarations over coarse
placeholders.
-/
