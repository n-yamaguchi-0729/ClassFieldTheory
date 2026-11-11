/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart_right.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Models.Gluing.OpensIsAffineOpenFiniteAevalTwoChart
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.OpensFinitePreimageSingletonToSpecPolynomial
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Util.WithWeakNamespace
public import Nyll.SchemeTheory.FunctionFields.StructureMorphism

/-!
# Scheme Opens isAffineOpen and finite aeval of twoChart right

Two-chart pole data makes the right coordinate chart affine and its polynomial evaluation map
finite, through the proper coordinate morphism and its field fibres.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Models.Gluing.Proofs
namespace Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart_right

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Polynomial

namespace AlgebraicGeometry

-- Keep the original proof-namespace entrypoints as aliases of the common owner.
export Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart.AlgebraicGeometry
  (SpecMap_mapRingHom_injective_of_quotient
    fibreField
    mem_range_SpecMap_fibreField
    transcendental_germToFunctionField_of_sections)

namespace Scheme

export Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart.AlgebraicGeometry.Scheme
  (comp_appTop'
    stalkClosedPointTo_germ_top)

end Scheme

namespace Scheme.Opens

export Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart.AlgebraicGeometry.Scheme.Opens
  (baseRingHom
    toSpecPolynomial
    toSpecPolynomial_comp_C
    ι_app_self_apply
    toSpecPolynomial_appTop_X
    ΓSpecIso_appTop_topIso_inv_eq
    valuativeCriterion_existence_toSpecPolynomial_of_twoChart
    isProper_toSpecPolynomial_of_twoChart
    finite_eval₂RingHom_of_twoChart
    ι_appTop_comp_topIso_hom
    topIso_hom_comp_baseRingHom
    finite_aeval_of_twoChart
    isProper_toSpecPolynomial_of_twoChart'
    bcSection
    resLE_toSpecPolynomial
    topIso_inv_resLE_appTop_topIso_hom
    bcSection_eq
    isAffineOpen_and_finite_aeval_of_twoChart_of_le
    isAffineOpen_and_finite_aeval_of_twoChart_impl
    isAffineOpen_and_finite_aeval_of_twoChart_right_impl)

end Scheme.Opens

end AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry in
with_weak_namespace _root_.AlgebraicCurves.Models.Gluing.Proofs
open Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart_right.AlgebraicGeometry in
with_weak_namespace Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart_right
open _root_.Polynomial in
theorem _root_.AlgebraicGeometry.Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_right
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec
      (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U V : C.Opens) (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hVU : U ⊓ V = C.basicOpen f)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hft : ∀ (K : Type u) [Field K] [Algebra R K],
      let _ := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ V);
      Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app V).hom g)) :
    IsAffineOpen V ∧
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
       (Polynomial.aeval g : R[X] →ₐ[R] Γ(C, V)).toRingHom.Finite) :=
  AlgebraicGeometry.Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_right_impl c U V f g
    hcov hVU hfg hft
end Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart_right
end AlgebraicCurves.Models.Gluing.Proofs
end ProofImplementation

attribute [-instance] AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp] AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
