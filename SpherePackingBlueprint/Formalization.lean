import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import SpherePacking.Basic.E8
import SpherePacking.Basic.PeriodicPacking
import SpherePacking.CohnElkies.LPBound
import SpherePacking.CohnElkies.Prereqs
import SpherePacking.MagicFunction.PolyFourierCoeffBound
import SpherePacking.MagicFunction.a.Eigenfunction
import SpherePacking.MagicFunction.a.SpecialValues
import SpherePacking.MagicFunction.b.Eigenfunction
import SpherePacking.MagicFunction.b.SpecialValues
import SpherePacking.MainTheorem
import SpherePacking.ModularForms.FG

set_option autoImplicit false

/-
Formalization surface cited by the Blueprint document.

This module is intentionally narrower than the upstream `SpherePacking`
umbrella, which also imports tactic experiments and tests that the document
does not reference.
-/

namespace BlueprintDocAliases

/-- The space of Schwartz functions. -/
abbrev SchwartzMap := _root_.SchwartzMap

/-- Modular forms of a given level and weight. -/
abbrev ModularForm := _root_.ModularForm

end BlueprintDocAliases
