/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Differentials.Local.Order
public import Nyll.AlgebraicCurves.Divisors.Maps.Maps

/-!
# Differentials, residues, and divisor correspondences

A chosen uniformizer in each place valuation ring and its order and nonvanishing properties.
-/

@[expose] public section

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem dCoord_eq : v.dCoord = KaehlerDifferential.D K F v.uniformizer := rfl

end Place

open scoped AlgebraicCurve.Place in
/-- The differential of the restricted place uniformizer in the extension field. -/
noncomputable def Place.restrictDCoord (F : Type*) {F' : Type*}
    [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    (w : Place K F') : Ω[F'⁄K] :=
  KaehlerDifferential.D K F' (algebraMap F F' (w.restrict F).uniformizer)

end AlgebraicCurve

end
