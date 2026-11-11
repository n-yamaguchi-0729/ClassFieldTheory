/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_IdealSheafModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Sheaves.IdealSheafModule
public import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.RelEffCartierDiv

/-!
# Ideal modules of relative effective Cartier divisors

The general ideal module is shared with SchemeTheory. The relative divisor
retains its original ideal module and dual line bundle.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

/-- The ideal module of the relative effective Cartier divisor. -/
abbrev RelEffCartierDiv.idealModule {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T : Scheme.{u}}
    {g : T ⟶ S} (D : RelEffCartierDiv f r g) : (pullback f g).Modules :=
  D.I.module

/-- The dual ideal module associated with the relative effective Cartier divisor. -/
abbrev RelEffCartierDiv.lineBundle {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T : Scheme.{u}}
    {g : T ⟶ S} (D : RelEffCartierDiv f r g) : (pullback f g).Modules :=
  D.I.invModule

end AlgebraicGeometry

end
