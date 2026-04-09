import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "TeX To Verso Porting Status" =>

:::group "porting_status"
Current harness status for the Sphere Packing in Lean Verso port.
:::

:::definition "tex_source_of_truth" (parent := "porting_status")
The TeX source of truth for the prose structure lives in
`./Sphere-Packing-LaTeX-Reference/blueprint/src/subsections/*.tex`.
:::

:::definition "porting_status_workflow" (parent := "porting_status")
The helper-managed harness now lives under `tools/verso-harness`. Direct-port
chapters should be validated with the LT audit stack before further prose
cleanup.
:::

:::definition "porting_status_snapshot" (parent := "porting_status")
The current direct-port chapters are `SpherePackings`, `PackingsDensity`,
`E8`, `FourierAnalysis`, `CohnElkies`, `ModularForms`, `MagicFunctions`, and
`ModularInequalities`. They predate the current adjacent-`tex` witness
requirement and should be treated as needing re-audit.
:::
