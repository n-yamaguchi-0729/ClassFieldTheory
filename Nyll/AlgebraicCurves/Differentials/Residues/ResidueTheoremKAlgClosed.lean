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

import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremKRatFunc
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremResidueTheoremK
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremResidueTheoremRatFunc
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTraceCompletionCommute
import Nyll.AlgebraicCurves.Divisors.Principal.InstHasCanonicalDivisorRatFuncPerfectField

/-!
# Differentials, residues, and divisor correspondences

The rational-function-field residue theorem and fibre trace identities give the residue theorem
over algebraically closed base fields.
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheoremK_of_isAlgClosed

noncomputable section

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.residueTheoremK_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [HasLocalResidue K F] [∀ w : Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [IsCurveOver K F] [IsCurveOver K (RatFunc K)]
    [∀ u : Place K (RatFunc K), u.FiniteResidue]
    [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]]
    [∀ v : Place K (RatFunc K), v.DCoordGenerates] : ResidueTheoremK K F := by
  classical
  let _ : HasCanonicalDivisor (K := K) (F := RatFunc K) :=
    AlgebraicCurve.instHasCanonicalDivisorRatFuncPerfectField K
  let _ : HasCanonicalLocalResidueKStar K F :=
    AlgebraicCurve.instHasCanonicalLocalResidueKStar
  let _ : HasCanonicalLocalResidueKStar K (RatFunc K) :=
    AlgebraicCurve.instHasCanonicalLocalResidueKStar
  have hP1K : ResidueTheoremK K (RatFunc K) :=
    AlgebraicCurve.residueTheoremK_ratFunc_of_isAlgClosed K
  have hP1 : ResidueTheorem K (RatFunc K) :=
    AlgebraicCurve.residueTheorem_of_residueTheoremK hP1K
  have hF : ResidueTheorem K F :=
    AlgebraicCurve.residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute
      hP1
      (AlgebraicCurve.residueTraceCompletionCommute
        (K := K) (F := F) (E := RatFunc K))
  exact AlgebraicCurve.residueTheoremK_of_residueTheorem_isAlgClosed (by intro _; exact hF)

end

end AlgebraicCurves.Differentials.Residues.Proofs.ResidueTheoremK_of_isAlgClosed
end ProofImplementation
