import SpherePackingBlueprint.TeXPrelude

set_option autoImplicit false

/-
Compatibility import shim for the blueprint chapters.

The chapters import this module for shared notation and toolchain-local
compatibility declarations only. Formalization declarations cited by the
document live behind `SpherePackingBlueprint.Formalization`, a narrower local
surface than the upstream `SpherePacking` umbrella module.
-/
