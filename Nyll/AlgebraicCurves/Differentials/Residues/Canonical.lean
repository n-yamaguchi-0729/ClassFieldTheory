/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstance.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Differentials.Residues.Basic
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Divisors.Maps.Maps
public import Nyll.AlgebraicCurves.Places.Completion
public import Nyll.AlgebraicCurves.Differentials.Residues.Construction
public import Nyll.AlgebraicCurves.Differentials.Kaehler.Weil

/-!
Results on Canonical.
-/
