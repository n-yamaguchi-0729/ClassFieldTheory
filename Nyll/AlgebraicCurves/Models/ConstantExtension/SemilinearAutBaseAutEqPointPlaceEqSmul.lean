/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Construction.Basic
import Nyll.AlgebraicCurves.Models.Points.AlgEquivPointPlaceCompHomEqAlgAutSmulPointPlace
import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear

/-!
# Curve Model exists semilinear Aut base Aut eq and point Equiv Place eq smul
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurve

universe u v

noncomputable section

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace CurveModel
open _root_.AlgebraicCurve.CurveModel
namespace GalPtSol
open _root_.AlgebraicCurve.CurveModel
open _root_.AlgebraicCurve


open _root_.AlgebraicCurves.Models.Proofs
open CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace
open AlgebraicCurve.CurveModel.ModelIndepSol.FunctionFieldPull

section

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y] [IsIntegral X] [IsIntegral Y]

theorem pull_baseToFunctionField_twist {K : Type u} [Field K] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K)) (τ : K ≃+* K)
    (hf : f ≫ cY = cX ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) (a : K) :
    pull f h (baseToFunctionField cY a) = baseToFunctionField cX (τ a) := by
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change pull f h (Y.presheaf.germ ⊤ (genericPoint Y) (TopologicalSpace.Opens.mem_top _) _) =
    X.presheaf.germ ⊤ (genericPoint X) (TopologicalSpace.Opens.mem_top _) _
  rw [pull_germ]
  have key : (f.app ⊤).hom (cY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
      cX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (τ a)) := by
    have h1 : (f.app ⊤).hom (cY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
        cX.appTop.hom ((Spec.map (CommRingCat.ofHom (τ : K →+* K))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) :=
      congrArg (fun φ => (Scheme.Hom.appTop φ).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
        a)) hf
    rw [h1]
    congr 1
    have h2 := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ :
      K →+* K)))
    exact h2.symm
  exact congrArg _ key

end

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- The function-field ring automorphism induced by an automorphism of the curve model. -/
def gRingEquiv (M : CurveModel K L) (e : M.C ≅ M.C) : L ≃+* L :=
  (M.ffEquiv.trans (equivOfIso e)).trans M.ffEquiv.symm

theorem gRingEquiv_apply (M : CurveModel K L) (e : M.C ≅ M.C) (a : L) :
    gRingEquiv M e a = M.ffEquiv.symm (equivOfIso e (M.ffEquiv a)) := rfl

theorem gRingEquiv_algebraMap (M : CurveModel K L) (e : M.C ≅ M.C) (τ : K ≃+* K)
    (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) (a : K) :
    gRingEquiv M e (algebraMap K L a) = algebraMap K L (τ a) := by
  rw [gRingEquiv_apply, M.ffEquiv_algebraMap, equivOfIso_apply,
    pull_baseToFunctionField_twist e.hom _ M.toBase M.toBase τ he a, ← M.ffEquiv_algebraMap,
    RingEquiv.symm_apply_apply]

/-- The semilinear function-field automorphism induced by a scheme automorphism over a base
automorphism. -/
def gSL (M : CurveModel K L) (e : M.C ≅ M.C) (τ : K ≃+* K)
    (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) : SemilinearAut
      K L :=
  ⟨(gRingEquiv M e, τ), fun a => gRingEquiv_algebraMap M e τ he a⟩

theorem gSL_smul (M : CurveModel K L) (e : M.C ≅ M.C) (τ : K ≃+* K)
    (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) (a : L) :
    gSL M e τ he • a = M.ffEquiv.symm (equivOfIso e (M.ffEquiv a)) := rfl

theorem baseAut_gSL (M : CurveModel K L) (e : M.C ≅ M.C) (τ : K ≃+* K)
    (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) :
    SemilinearAut.baseAut (gSL M e τ he) = τ := rfl

theorem germ_clause (M : CurveModel K L) (e : M.C ≅ M.C) (τ : K ≃+* K)
    (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K)))
    (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (e.hom
      ⁻¹ᵁ U))]
    (t : Γ(M.C, U)) :
    gSL M e τ he • M.ffEquiv.symm (M.C.germToFunctionField U t) =
      M.ffEquiv.symm (M.C.germToFunctionField (e.hom ⁻¹ᵁ U) ((e.hom.app U).hom t)) := by
  rw [gSL_smul, RingEquiv.apply_symm_apply, equivOfIso_apply]
  congr 1
  exact pull_germ e.hom (specializes_of_iso e) U _ t

theorem coe_toValuationSubring_pointEquivPlace [IsAlgClosed K] (M : CurveModel K L)
    (x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    ((M.pointEquivPlace x).toValuationSubring : Set L) =
      M.ffEquiv.symm '' ((algebraMap (M.C.presheaf.stalk (x.1.base (IsLocalRing.closedPoint K)))
        M.C.functionField).range : Set M.C.functionField) := by
  rw [CurveModel.pointEquivPlace_apply]
  have h := M.range_stalk_eq (pointEquivClosedPoint M.toBase x)
  rw [← RingHom.map_range] at h
  have h' := congrArg (fun S : Subring L => (S : Set L)) h
  simp only [Subring.coe_map] at h'
  exact h'.symm

theorem point_clause [IsAlgClosed K] (M : CurveModel K L) (e : M.C ≅ M.C) (τ : K ≃+* K)
    (he : e.hom ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K)))
    (x y : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _})
    (hxy : y.1 ≫ e.hom = Spec.map (CommRingCat.ofHom (τ : K →+* K)) ≫ x.1) :
    M.pointEquivPlace y = gSL M e τ he • M.pointEquivPlace x := by
  apply Place.ext
  apply SetLike.coe_injective
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.coe_pointwise_smul, ← Set.image_smul,
    coe_toValuationSubring_pointEquivPlace, coe_toValuationSubring_pointEquivPlace, ←
      Set.image_comp]
  have hcomp : ((fun m => gSL M e τ he • m) ∘ (M.ffEquiv.symm : M.C.functionField → L)) =
      (M.ffEquiv.symm : M.C.functionField → L) ∘ (equivOfIso e) := by
    funext a
    change gRingEquiv M e (M.ffEquiv.symm a) = M.ffEquiv.symm (equivOfIso e a)
    rw [gRingEquiv_apply, RingEquiv.apply_symm_apply]
  rw [hcomp, Set.image_comp]
  have hpt : e.hom.base (y.1.base (IsLocalRing.closedPoint K)) = x.1.base (IsLocalRing.closedPoint
    K) := by
    have h1 : e.hom.base (y.1.base (IsLocalRing.closedPoint K)) =
        x.1.base ((Spec.map (CommRingCat.ofHom (τ : K →+* K))).base (IsLocalRing.closedPoint K)) :=
      congrArg (fun φ : Spec (CommRingCat.of K) ⟶ M.C => φ.base (IsLocalRing.closedPoint K)) hxy
    rw [h1]
    congr 1
    have : Subsingleton (PrimeSpectrum K) := inferInstance
    exact Subsingleton.elim _ _
  rw [← hpt, image_equivOfIso_range_stalk e]

end AlgebraicCurve.CurveModel.GalPtSol

end

open AlgebraicCurve.CurveModel.GalPtSol in
theorem _root_.AlgebraicCurve.CurveModel.exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul
    {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : AlgebraicCurve.CurveModel K L) (τ : K ≃+* K) (h : M.C ⟶ M.C) [IsIso h]
    (hh : h ≫ M.toBase = M.toBase ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) :
    ∃ g : AlgebraicCurve.SemilinearAut K L,
      AlgebraicCurve.SemilinearAut.baseAut g = τ ∧
      (∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty (Scheme.Opens.toScheme (h
        ⁻¹ᵁ U))]
        (t : Γ(M.C, U)),
        g • M.ffEquiv.symm (M.C.germToFunctionField U t) =
          M.ffEquiv.symm (M.C.germToFunctionField (h ⁻¹ᵁ U) ((h.app U).hom t))) ∧
      ∀ x y : {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _},
        y.1 ≫ h = Spec.map (CommRingCat.ofHom (τ : K →+* K)) ≫ x.1 →
          M.pointEquivPlace y = g • M.pointEquivPlace x :=
  ⟨gSL M (asIso h) τ hh, baseAut_gSL M (asIso h) τ hh,
    fun U hU hU' t => by
      have : Nonempty (Scheme.Opens.toScheme ((asIso h).hom ⁻¹ᵁ U)) := hU'
      exact germ_clause M (asIso h) τ hh U t,
    fun x y hxy => point_clause M (asIso h) τ hh x y hxy⟩
end CurveModel_exists_semilinearAut_baseAut_eq_and_pointEquivPlace_eq_smul
end AlgebraicCurves.Models.Proofs
end ProofImplementation
