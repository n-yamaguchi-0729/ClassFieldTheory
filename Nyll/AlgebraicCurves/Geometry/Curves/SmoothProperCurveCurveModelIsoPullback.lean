/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Models.Construction.Basic
import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Models.Construction.CurveIsIntegral
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.EssFiniteTypeFunctionField
import Nyll.AlgebraicCurves.Places.ValuationRings.RangeStalkEq
import Nyll.AlgebraicCurves.Models.LocalGeometry.EqRangeStalkEq
import Nyll.AlgebraicCurves.Models.LocalGeometry.ClosedPointRangeStalkEq
import Nyll.AlgebraicCurves.Models.Charts.IsAffineOpenMemFinset
import Nyll.AlgebraicCurves.Models.Charts.IsAffineOpenMemFinsetField

/-!
# Curve-model isomorphisms for perfect-field fibres

The pullback of a smooth proper curve to a perfect field is isomorphic
over that field to the scheme of a curve model.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed
open
  _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp]
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp]
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd
  AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply
  AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one
  AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec
  AlgebraicCurve.PoleDivisorPackage.mk.injEq

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
    NeronModelInfra AlgebraicCurve

theorem _root_.AlgebraicGeometry.SmoothProperCurve.exists_curveModel_iso_pullback_of_perfectField
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (k : Type u) [Field k] [PerfectField k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : IsCurveOver k L) (_ :
        Algebra.EssFiniteType k L)
      (M : CurveModel k L) (e : M.C ≅ pullback c s), e.hom ≫ pullback.snd c s = M.toBase := by
  classical
  let Cs : Scheme.{u} := pullback c s
  let cs : Cs ⟶ Spec (CommRingCat.of k) := pullback.snd c s
  have : IsIntegral Cs := SmoothProperCurve.isIntegral_pullback_Spec_field R c s
  have : IsProper cs := inferInstance
  have : SmoothOfRelativeDimension 1 cs := inferInstance
  let alg : Algebra k Cs.functionField := (baseToFunctionField cs).toAlgebra
  have hco : IsCurveOver k Cs.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cs (RingEquiv.refl _) (fun _ => rfl)
  have hft : Algebra.EssFiniteType k Cs.functionField := essFiniteType_functionField cs
  refine ⟨Cs.functionField, inferInstance, alg, hco, hft,
    CurveModel.ofSmoothProperCurve cs, Iso.refl _, ?_⟩
  exact Category.id_comp cs

/-- The algebraically closed specialization of the perfect-field construction. -/
theorem _root_.AlgebraicGeometry.SmoothProperCurve.exists_curveModel_iso_pullback_of_isAlgClosed
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : IsCurveOver k L) (_ :
        Algebra.EssFiniteType k L)
      (M : CurveModel k L) (e : M.C ≅ pullback c s), e.hom ≫ pullback.snd c s = M.toBase :=
  exists_curveModel_iso_pullback_of_perfectField R c k s

end SmoothProperCurve_exists_curveModel_iso_pullback_of_isAlgClosed
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation
