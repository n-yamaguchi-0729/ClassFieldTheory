/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.RationalCuspDecompositionConstants
public import Nyll.EtaleFundamentalGroups.Inertia.InertiaConjugateImage
public import Nyll.EtaleFundamentalGroups.GeometricFiber.SourceIsoGalois
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldSourceGaloisPoint

/-! # RationalCuspArithmeticNormalizer -/

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale SchemeTheory
open scoped Pointwise

namespace AlgebraicGeometry.FiniteEtale
universe u

/-- The actual generic arithmetic map labels field automorphisms by their
constant restriction, with exactly one fixed inner base-point correction. -/
theorem exists_fieldSource_arithmetic_restriction_label
    (k F κ Ω : Type u) [Field k] [Field F] [Field κ] [Field Ω]
    [Algebra k F] [Algebra k κ] [Algebra k Ω]
    [Algebra F Ω] [Algebra κ Ω]
    [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
    [IsSepClosure k κ] [IsSepClosure F Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (j : Spec (.of F) ⟶ X)
    (hbase : (ξ F Ω ≫ j) ≫ f = ξ k Ω) :
    ∃ α : Gal(κ/k), ∀ γ : Gal(Ω/F),
      arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ j)
        (fieldSourceAbsoluteGaloisHom F Ω j γ) =
      α * (γ.restrictScalars k).restrictNormal κ * α⁻¹ := by
  obtain ⟨α, hα⟩ := arithmeticFundamentalGroupHom_sourceAction k κ Ω f
    (ξ F Ω ≫ j) hbase
  refine ⟨α, ?_⟩
  intro γ
  let e := Scheme.Spec.mapIso γ.toRingEquiv.toCommRingCatIso.op
  have hfix : e.hom ≫ ξ F Ω = ξ F Ω := by
    change Spec.map (CommRingCat.ofHom γ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) = _
    rw [← Spec.map_comp]
    exact congrArg (fun z : F →+* Ω => Spec.map (CommRingCat.ofHom z))
      γ.toAlgHom.comp_algebraMap
  have hsource : e.hom ≫ (ξ F Ω ≫ j) = ξ F Ω ≫ j := by
    rw [← Category.assoc, hfix]
  have hρ : γ.toRingHom.comp (algebraMap κ Ω) =
      (algebraMap κ Ω).comp ((γ.restrictScalars k).restrictNormal κ).toRingHom := by
    ext x
    exact ((γ.restrictScalars k).restrictNormal_commutes κ x).symm
  have hq : fieldSourceAbsoluteGaloisHom F Ω j γ =
      Aut.of (fiberSourceIso (ξ F Ω ≫ j) e ≪≫ eqToIso (congrArg fiber hsource)) := by
    apply Aut.ext
    apply Iso.ext
    ext W w
    apply (fiberObjEquivHom (ξ F Ω ≫ j) W).injective
    apply Over.OverMorphism.ext
    exact (fundamentalGroupHom_point_of_point_action j (ξ F Ω)
      (suppliedGaloisEquivFundamentalGroup F Ω γ) γ.toRingHom
      (suppliedGaloisEquivFundamentalGroup_point F Ω γ) W w).trans
      (fiberSourceIso_aut_point (ξ F Ω ≫ j) e hsource W w).symm
  rw [hq]
  exact hα e γ.toRingHom rfl ((γ.restrictScalars k).restrictNormal κ) hρ hsource

end AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.Inertia
universe u
attribute [local instance] normalizationCommAlgGaloisAction

/-- Each prescribed G_k element has a lift normalizing the same actual
arithmetic normalization inertia image. The correction α is retained. -/
theorem rationalCusp_arithmetic_normalizer_full_image
    (k A F κ Ω : Type u)
    [Field k] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Field κ] [Field Ω]
    [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
    [Algebra A F] [IsFractionRing A F]
    [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
    [IsScalarTower A F Ω] [IsScalarTower k A Ω]
    [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
    [IsGalois F Ω] [IsAlgClosed κ] [IsAlgClosure k κ]
    [IsSepClosure k κ] [IsSepClosure F Ω] [IsSepClosed Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    (r : A →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal A)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (j : Spec (.of F) ⟶ X)
    (hbase : (ξ F Ω ≫ j) ≫ f = ξ k Ω) :
    let q := fieldSourceAbsoluteGaloisHom F Ω j
    let I := (Q.inertia Gal(Ω/F)).map q.toMonoidHom
    ∀ τ : Gal(κ/k), ∃ γ : Aut (fiber (ξ F Ω ≫ j)),
      γ ∈ Subgroup.normalizer (I : Set _) ∧
      arithmeticFundamentalGroupHom k κ f (ξ F Ω ≫ j) γ = τ := by
  intro q I
  obtain ⟨α, hα⟩ := exists_fieldSource_arithmetic_restriction_label k F κ Ω f j hbase
  intro τ
  obtain ⟨d, hd⟩ := exists_normalizationDecomposition_lift_constants k A F κ Ω
    Q r hr (α⁻¹ * τ * α)
  refine ⟨q d.val, ?_, ?_⟩
  · have hQ : d.val • Q = Q := d.property
    have hI : I.map (MulAut.conj (q d.val)).toMonoidHom = I := by
      have hmap := inertia_smul_map (M := Gal(Ω/F)) Q
        (d.val : Gal(Ω/F)) q.toMonoidHom
      rw [hQ] at hmap
      exact hmap.symm
    apply Subgroup.mem_set_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      rw [← hI]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hI] at hx
      obtain ⟨y, hy, heq⟩ := hx
      exact (MulAut.conj (q d.val)).injective heq ▸ hy
  · rw [hα d.val, hd]
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end EtaleFundamentalGroups.Inertia
