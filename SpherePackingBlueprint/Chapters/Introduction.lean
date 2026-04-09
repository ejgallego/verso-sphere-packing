import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Introduction" =>

:::group "main_story"
Landing page for the current Sphere Packing in Lean Verso harness.
:::

:::definition "verso_port_scope" (parent := "main_story")
The prose source of truth remains the upstream TeX blueprint under
`Sphere-Packing-LaTeX-Reference/blueprint/src/subsections`. The existing Verso
chapters in this repository are the direct-port material that now needs to be
re-audited under the current source-paired LT workflow.
:::

:::definition "verso_port_route" (parent := "main_story")
The mathematical route follows the upstream blueprint: sphere packings and
density formulas, the `E_8` lattice, Fourier analysis, the Cohn-Elkies bound,
modular forms, the magic functions `a` and `b`, and the final modular
inequalities.
:::
