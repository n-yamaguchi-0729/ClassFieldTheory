/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus.AdelicGenus
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Duality.FinrankOmegaSpaceEqEllCanonicalSub
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Index.RiemannGenusReachedStichtenothGenusExists
import Nyll.AlgebraicCurves.Differentials.Residues.ResidueTheoremResidueTheoremK
import Nyll.AlgebraicCurves.Differentials.Residues.WeilKaehlerAgreeResidueTheorem
import Nyll.AlgebraicCurves.FunctionFields.Constants.ConstantsAreBaseAlgClosed
import Nyll.AlgebraicCurves.Places.Rational.RatFuncStichtenothGenusExists
import Mathlib.Tactic.Linarith

/-!
Function-field Riemann–Roch from the residue theorem over algebraically closed constants.
The canonical residue comparison, attained genus and adelic index formula share their existing
implementations; no independent completion or pole-divisor construction is needed here.
-/

open AlgebraicCurve KaehlerDifferential

theorem _root_.AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F]
    (hRTK : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F := by
  intro hCurve hCanonical hCoordinates
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed K F
  have hSG : StichtenothGenusExists K F :=
    RationalFunctionField.stichtenothGenusExists K F hC
  have : Nonempty (Place K F) := hSG.1
  have : FiniteDimensional K (LSpace (0 : Divisor K F)) := hSG.2.1
  have hWK : WeilKaehlerAgree K F :=
    weilKaehlerAgree_of_residueTheorem (residueTheorem_of_residueTheoremK hRTK)
  obtain ⟨_, _, D₀, hD₀⟩ :=
    riemannGenusReached_of_stichtenothGenusExists hSG hWK hC
  intro ω hω D
  have hIndex := (indexOfSpecialty_eq_of_genusReached hD₀ D).2
  have hDual := finrank_omegaSpace_eq_ell_canonical_sub_of_genusReached hD₀ hWK hω D
  rw [finrank_omegaSpace_eq_indexOfSpecialty] at hDual
  rw [hDual] at hIndex
  linarith
