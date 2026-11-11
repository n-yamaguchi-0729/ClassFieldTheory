/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremRatFuncPerfectField
public import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremResidueTheoremK
public import Nyll.AlgebraicCurves.Differentials.Residues.Construction
public import Nyll.AlgebraicCurves.FunctionFields.Rational.InstIsCurveOverRatFunc
public import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
public import Nyll.AlgebraicCurves.Differentials.Residues.Basic

/-!
# The residue theorem over an algebraically closed rational-function field

The perfect-field theorem supplies the residue sum for the canonical family. Uniqueness of
normalized local residue data over an algebraically closed field gives the theorem for every
residue family.
-/

@[expose] public section

open _root_.AlgebraicCurve
open AlgebraicCurves.Differentials.Residues.Proofs

theorem _root_.AlgebraicCurve.residueTheoremK_ratFunc_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K (RatFunc K)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K (RatFunc K) := by
  classical
  have : IsCurveOver K (RatFunc K) := instIsCurveOverRatFunc K
  have : Nontrivial Ω[(RatFunc K)⁄K] := IsCurveOver.instNontrivialKaehler
  have : ∀ v : Place K (RatFunc K), v.FiniteResidue :=
    fun v => ⟨IsCurveOver.finiteResidue v⟩
  let : HasCanonicalLocalResidueKStar K (RatFunc K) :=
    instHasCanonicalLocalResidueKStar
  apply ResidueTheoremK_of_isAlgClosed.AlgebraicCurve.residueTheoremK_of_residueTheorem_isAlgClosed
  intro _hPD
  exact residueTheorem_ratFunc_of_perfectField K
