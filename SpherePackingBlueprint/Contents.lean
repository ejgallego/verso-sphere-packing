import Verso
import VersoManual
import VersoBlueprint

import SpherePackingBlueprint.TeXPrelude
import SpherePackingBlueprint.Bibliography
import SpherePackingBlueprint.Chapters.Introduction
import SpherePackingBlueprint.Chapters.SpherePackings
import SpherePackingBlueprint.Chapters.PackingsDensity
import SpherePackingBlueprint.Chapters.E8
import SpherePackingBlueprint.Chapters.FourierAnalysis
import SpherePackingBlueprint.Chapters.CohnElkies
import SpherePackingBlueprint.Chapters.ModularForms
import SpherePackingBlueprint.Chapters.MagicFunctions
import SpherePackingBlueprint.Chapters.ModularInequalities
import SpherePackingBlueprint.Chapters.PortingStatus

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option pp.rawOnError true
set_option linter.style.longLine false


#doc (Manual) "Sphere Packing in Lean" =>

%%%
shortTitle := "Sphere Packing in R^8"
authors := ["Maryna Viazovska", "Sphere Packing in Lean collaborators"]
%%%

# Overview

This document ports the original Sphere Packing in Lean TeX blueprint to
Verso Blueprints and tracks the same mathematical narrative.

The project formalizes Maryna Viazovska's theorem that no packing of unit
balls in $`\mathbb{R}^8` has density greater than the $`E_8` lattice packing;
see {citet Via2017}[]. The global upper bound comes from the linear
programming method of {citet ElkiesCohn}[], and the crucial input is an
explicit optimal auxiliary function built from modular forms.

Compared with the upstream TeX source, this Verso copy reorganizes the
blueprint into linked nodes and groups so that the dependency graph and summary
are rendered directly from the structured document.

{include 0 SpherePackingBlueprint.Chapters.Introduction}
{include 0 SpherePackingBlueprint.Chapters.SpherePackings}
{include 0 SpherePackingBlueprint.Chapters.PackingsDensity}
{include 0 SpherePackingBlueprint.Chapters.E8}
{include 0 SpherePackingBlueprint.Chapters.FourierAnalysis}
{include 0 SpherePackingBlueprint.Chapters.CohnElkies}
{include 0 SpherePackingBlueprint.Chapters.ModularForms}
{include 0 SpherePackingBlueprint.Chapters.MagicFunctions}
{include 0 SpherePackingBlueprint.Chapters.ModularInequalities}
{include 0 SpherePackingBlueprint.Chapters.PortingStatus}

{blueprint_graph}

{blueprint_summary}

{blueprint_bibliography}
