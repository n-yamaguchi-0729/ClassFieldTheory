/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.SchemeTheory.Modules.Functoriality.AffinePullbackSections
public import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech

/-!
Scalar-extension equivalences of affine-chart rings and the induced two-chart Cech kernel and
cokernel maps.
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace TwoAffineBaseChange

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace CechBaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
variable (A : Type u) [CommRing A] [Algebra R A]

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange (XA fst snd)

theorem restrict_compat {U V : X.Opens} (hVU : V ≤ U)
    (eU : letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
      (A ⊗[R] Γ(X, U)) ≃ₐ[A] Γ(XA c A, (fst c A) ⁻¹ᵁ U))
    (heU : letI := algebraOfHom c U; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U)
      ∀ s : Γ(X, U), eU ((1 : A) ⊗ₜ[R] s) = ((fst c A).app U).hom s)
    (eV : letI := algebraOfHom c V; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ V)
      (A ⊗[R] Γ(X, V)) ≃ₐ[A] Γ(XA c A, (fst c A) ⁻¹ᵁ V))
    (heV : letI := algebraOfHom c V; letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ V)
      ∀ s : Γ(X, V), eV ((1 : A) ⊗ₜ[R] s) = ((fst c A).app V).hom s)
    (x : letI := algebraOfHom c U; A ⊗[R] Γ(X, U)) :
    letI := algebraOfHom c U; letI := algebraOfHom c V
    letI := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U); letI := algebraOfHom (snd c A) ((fst c A)
      ⁻¹ᵁ V)
    eV ((restrictAlgHom c hVU).toLinearMap.baseChange A x)
      = ((XA c A).presheaf.map (homOfLE ((fst c A).preimage_mono hVU)).op).hom (eU x) := by
  let := algebraOfHom c U; let := algebraOfHom c V
  let := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ U); let := algebraOfHom (snd c A) ((fst c A) ⁻¹ᵁ V)
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    have ha : a ⊗ₜ[R] s = a • ((1 : A) ⊗ₜ[R] s) := by rw [TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
    rw [LinearMap.baseChange_tmul, AlgHom.toLinearMap_apply, ha, map_smul, heU]
    have ha' : a ⊗ₜ[R] (restrictAlgHom c hVU s) = a • ((1 : A) ⊗ₜ[R] (restrictAlgHom c hVU s)) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [ha', map_smul, heV]
    have hnat : ((fst c A).app V).hom (restrictAlgHom c hVU s)
        = ((XA c A).presheaf.map (homOfLE ((fst c A).preimage_mono hVU)).op).hom (((fst c A).app
          U).hom s) := by
      change (X.presheaf.map (homOfLE hVU).op ≫ (fst c A).app V).hom s = _
      rw [Scheme.Hom.naturality]
      rfl
    rw [hnat, Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    change ((snd c A).appLE ⊤ ((fst c A) ⁻¹ᵁ V) le_top).hom _
      = ((XA c A).presheaf.map _).hom (((snd c A).appLE ⊤ ((fst c A) ⁻¹ᵁ U) le_top).hom _)
    have hmap := Scheme.Hom.appLE_map (snd c A)
      (U := ⊤) (V := (fst c A) ⁻¹ᵁ U) (V' := (fst c A) ⁻¹ᵁ V)
      le_top (homOfLE ((fst c A).preimage_mono hVU)).op
    exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hmap)
      ((Scheme.ΓSpecIso (.of A)).inv.hom a)).symm.trans (CommRingCat.comp_apply _ _ _)

section Cech

variable (𝒱 : X.TwoAffineOpenCover)

/-- The two-chart section complex of the scalar-extended structure sheaf. -/
abbrev SA : TwoChartCech.Sections ((𝒱.pullback c A).cover (snd c A)) :=
  (𝒱.pullback c A).structureSheafSections (snd c A)

/-- Compatible base-algebra equivalences for the two chart rings and their intersection after
scalar extension.
-/
structure BaseChangeIsos where
  /-- The scalar-extension equivalence for the first chart ring. -/
  e0 : (A ⊗[R] (𝒱.cover c).A0) ≃ₐ[A] ((𝒱.pullback c A).cover (snd c A)).A0
  /-- The scalar-extension equivalence for the second chart ring. -/
  e1 : (A ⊗[R] (𝒱.cover c).A1) ≃ₐ[A] ((𝒱.pullback c A).cover (snd c A)).A1
  /-- The scalar-extension equivalence for the intersection ring. -/
  e01 : (A ⊗[R] (𝒱.cover c).A01) ≃ₐ[A] ((𝒱.pullback c A).cover (snd c A)).A01
  /-- The first chart equivalence agrees with pullback on original sections. -/
  he0 : ∀ s : (𝒱.cover c).A0, e0 ((1 : A) ⊗ₜ[R] s) = ((fst c A).app 𝒱.U0).hom s
  /-- The second chart equivalence agrees with pullback on original sections. -/
  he1 : ∀ s : (𝒱.cover c).A1, e1 ((1 : A) ⊗ₜ[R] s) = ((fst c A).app 𝒱.U1).hom s
  /-- The intersection equivalence agrees with pullback on original sections. -/
  he01 : ∀ s : (𝒱.cover c).A01, e01 ((1 : A) ⊗ₜ[R] s) = ((fst c A).app (𝒱.U0 ⊓ 𝒱.U1)).hom s

namespace BaseChangeIsos

variable {c A 𝒱} (E : BaseChangeIsos c A 𝒱)

theorem e01_ρ0 (x : A ⊗[R] (𝒱.cover c).A0) :
    E.e01 ((𝒱.cover c).ρ0.toLinearMap.baseChange A x) = ((𝒱.pullback c A).cover (snd c A)).ρ0
      (E.e0 x) :=
  restrict_compat c A (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0) E.e0 E.he0 E.e01 E.he01 x

theorem e01_ρ1 (x : A ⊗[R] (𝒱.cover c).A1) :
    E.e01 ((𝒱.cover c).ρ1.toLinearMap.baseChange A x) = ((𝒱.pullback c A).cover (snd c A)).ρ1
      (E.e1 x) :=
  restrict_compat c A (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1) E.e1 E.he1 E.e01 E.he01 x

theorem cechDiff_structureSheaf_apply {R' : Type u} [CommRing R'] (𝒰 : TwoChartCech.Cover.{u, u} R')
    (s : 𝒰.A0 × 𝒰.A1) : 𝒰.structureSheaf.cechDiff s = 𝒰.ρ1 s.2 - 𝒰.ρ0 s.1 := by
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r1_apply,
    TwoChartCech.Cover.lineBundle_r0_apply, Units.val_one, one_mul]

theorem e01_cechDiff_baseChange (x : A ⊗[R] ((𝒱.cover c).A0 × (𝒱.cover c).A1)) :
    E.e01 (((𝒱.structureSheafSections c).cechDiff.baseChange A) x)
      = (SA c A 𝒱).cechDiff
          (E.e0 (TensorProduct.prodRight R A A _ _ x).1, E.e1 (TensorProduct.prodRight R A A _ _
            x).2) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, Prod.fst_add, Prod.snd_add, hx, hy]
    rw [← map_add]; rfl
  | tmul a s =>
    rw [LinearMap.baseChange_tmul, cechDiff_structureSheaf_apply, TensorProduct.prodRight_tmul,
      cechDiff_structureSheaf_apply, TensorProduct.tmul_sub, map_sub]
    have h1 := E.e01_ρ1 (a ⊗ₜ[R] s.2)
    have h0 := E.e01_ρ0 (a ⊗ₜ[R] s.1)
    rw [LinearMap.baseChange_tmul] at h1 h0
    exact congrArg₂ (· - ·) h1 h0

theorem mem_ker_baseChange_iff (x : A ⊗[R] ((𝒱.cover c).A0 × (𝒱.cover c).A1)) :
    x ∈ LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange A)
      ↔ (E.e0 (TensorProduct.prodRight R A A _ _ x).1, E.e1 (TensorProduct.prodRight R A A _ _ x).2)
          ∈ (SA c A 𝒱).H0 := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← e01_cechDiff_baseChange,
    ← map_zero E.e01, E.e01.injective.eq_iff]

/-- The linear map on pairs of chart sections induced by the two scalar-extension
equivalences.
-/
def pairMap : (A ⊗[R] ((𝒱.cover c).A0 × (𝒱.cover c).A1)) →ₗ[A]
    (((𝒱.pullback c A).cover (snd c A)).A0 × ((𝒱.pullback c A).cover (snd c A)).A1) :=
  (E.e0.toLinearEquiv.toLinearMap.prodMap E.e1.toLinearEquiv.toLinearMap) ∘ₗ
    (TensorProduct.prodRight R A A _ _).toLinearMap

theorem pairMap_apply (x : A ⊗[R] ((𝒱.cover c).A0 × (𝒱.cover c).A1)) :
    E.pairMap x = (E.e0 (TensorProduct.prodRight R A A _ _ x).1, E.e1 (TensorProduct.prodRight R
      A A _ _ x).2) :=
  rfl

theorem pairMap_bijective : Function.Bijective E.pairMap := by
  constructor
  · intro x y h
    apply (TensorProduct.prodRight R A A _ _).injective
    rw [pairMap_apply, pairMap_apply, Prod.mk.injEq] at h
    exact Prod.ext (E.e0.injective h.1) (E.e1.injective h.2)
  · rintro ⟨p0, p1⟩
    obtain ⟨x0, rfl⟩ := E.e0.surjective p0
    obtain ⟨x1, rfl⟩ := E.e1.surjective p1
    refine ⟨(TensorProduct.prodRight R A A _ _).symm (x0, x1), ?_⟩
    rw [pairMap_apply, LinearEquiv.apply_symm_apply]

/-- The linear map from the base-changed Cech kernel to degree-zero Cech cohomology. -/
def kerToH0 : LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange A) →ₗ[A] (SA c A
    𝒱).H0 :=
  E.pairMap.restrict fun x hx => by rw [pairMap_apply]; exact (E.mem_ker_baseChange_iff x).mp hx

theorem kerToH0_bijective : Function.Bijective E.kerToH0 := by
  constructor
  · intro x y h
    exact Subtype.ext (E.pairMap_bijective.1 (congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := E.pairMap_bijective.2 y
    exact ⟨⟨x, (E.mem_ker_baseChange_iff x).mpr (by rwa [pairMap_apply] at hy)⟩, rfl⟩

/-- The linear equivalence from the base-changed Cech kernel to degree-zero Cech cohomology. -/
def kerEquivH0 : LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange A) ≃ₗ[A] (SA c
    A 𝒱).H0 :=
  LinearEquiv.ofBijective _ E.kerToH0_bijective

theorem kerEquivH0_apply_coe (x : LinearMap.ker ((𝒱.structureSheafSections
    c).cechDiff.baseChange A)) :
    ((E.kerEquivH0 x : (SA c A 𝒱).M0 × (SA c A 𝒱).M1))
      = (E.e0 (TensorProduct.prodRight R A A _ _ x.1).1, E.e1 (TensorProduct.prodRight R A A _ _
        x.1).2) :=
  rfl

/-- The linear equivalence from the base-changed Cech cokernel to degree-one Cech cohomology. -/
def cokerEquivH1 :
    ((A ⊗[R] (𝒱.cover c).A01) ⧸ LinearMap.range ((𝒱.structureSheafSections
      c).cechDiff.baseChange A))
      ≃ₗ[A] (SA c A 𝒱).H1 :=
  Submodule.Quotient.equiv _ _ E.e01.toLinearEquiv (by
    apply le_antisymm
    · rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
      refine ⟨E.pairMap x, ?_⟩
      change (SA c A 𝒱).cechDiff (E.pairMap x) = E.e01 _
      rw [pairMap_apply, ← e01_cechDiff_baseChange]
    · rintro y ⟨p, rfl⟩
      obtain ⟨x, rfl⟩ := E.pairMap_bijective.2 p
      refine ⟨((𝒱.structureSheafSections c).cechDiff.baseChange A) x, LinearMap.mem_range_self _
        _, ?_⟩
      change E.e01 _ = (SA c A 𝒱).cechDiff (E.pairMap x)
      rw [pairMap_apply, e01_cechDiff_baseChange])

end BaseChangeIsos

end Cech

end CechBaseChange

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.TensorProduct
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

open _root_.AlgebraicGeometry.Scheme
  (exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen) in
theorem _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (e0 : (A ⊗[R] (𝒱.cover c).A0) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A0)
      (e1 : (A ⊗[R] (𝒱.cover c).A1) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A1)
      (e01 : (A ⊗[R] (𝒱.cover c).A01) ≃ₐ[A]
          ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
      (eH0 : LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange A) ≃ₗ[A]
          ((𝒱.pullback c A).structureSheafSections
            (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H0)
      (eH1 : ((A ⊗[R] (𝒱.cover c).A01) ⧸ LinearMap.range ((𝒱.structureSheafSections
        c).cechDiff.baseChange A))
          ≃ₗ[A] ((𝒱.pullback c A).structureSheafSections
            (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H1),
      (∀ s, e0 ((1 : A) ⊗ₜ[R] s) = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app
        𝒱.U0).hom s) ∧
      (∀ s, e1 ((1 : A) ⊗ₜ[R] s) = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app
        𝒱.U1).hom s) ∧
      (∀ s, e01 ((1 : A) ⊗ₜ[R] s)
          = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) ∧
      (∀ x, ((eH0 x : _ × _)) = (e0 (TensorProduct.prodRight R A A _ _ x.1).1,
          e1 (TensorProduct.prodRight R A A _ _ x.1).2)) ∧
      (∀ y, eH1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (e01 y)) := by
  obtain ⟨e0, he0⟩ :=
    exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
      c 𝒱.U0 𝒱.isAffineOpen_U0 A
  obtain ⟨e1, he1⟩ :=
    exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
      c 𝒱.U1 𝒱.isAffineOpen_U1 A
  obtain ⟨e01, he01⟩ :=
    exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
      c (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf A
  let E : AlgebraicGeometry.Scheme.TwoAffineOpenCover.CechBaseChange.BaseChangeIsos c A 𝒱 :=
    { e0 := e0, e1 := e1, e01 := e01, he0 := he0, he1 := he1, he01 := he01 }
  exact ⟨e0, e1, e01, E.kerEquivH0, E.cokerEquivH1, he0, he1, he01, fun x => rfl, fun y => rfl⟩

end
end TwoAffineBaseChange
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
