/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FunctionFields.GeometricFullConstants
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.GeometricConstantExtension
public import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFields.FunctionFieldConstantExtensionScalars
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveCurveModelIsoPullbackFunctionFieldGermEq
public import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralAlgClosed
public import Nyll.AlgebraicCurves.Models.FunctionFields.CurveModelIsoFieldEquivSymmFunctionFieldGermEq
public import Nyll.SchemeTheory.RingTheory.FieldExtensions.SeparableConstantsTensor
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The actual geometric compositum and the original base-changed scheme

Geometric integrality of the original supplied generic source proves that its
separable constants already lie in the base. The original function field
tensored with the actual separable constant field is therefore a field. Its
two literal tensor maps identify the actual compositum with the function field
of the original base change. The resulting equivalence preserves the original
constant inclusion and the original germs.
-/

@[expose] public section

universe u

noncomputable section

open scoped TensorProduct

namespace FunctionField

section TensorComparison

variable {k F C L : Type*} [Field k] [Field F] [Field C] [Field L]
    [Algebra k F] [Algebra k C] [Algebra.IsSeparable k C]
    [Algebra k L] [Algebra C L] [IsScalarTower k C L]

private theorem tensorLift_bijective_of_constant_generation
    (f : F →ₐ[k] L)
    (hsc : ∀ x : F, IsSeparable k x → x ∈ (algebraMap k F).range)
    (hgen : IntermediateField.adjoin C (Set.range f) = ⊤) :
    Function.Bijective
      (Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom k C L)
        (fun _ _ => Commute.all _ _)) := by
  let fieldTensor : Field (F ⊗[k] C) :=
    (Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range
      k F C hsc).toField
  let q : F ⊗[k] C →ₐ[k] L :=
    Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom k C L)
      (fun _ _ => Commute.all _ _)
  have hC (a : C) : algebraMap C L a ∈ q.toRingHom.fieldRange := by
    refine ⟨1 ⊗ₜ[k] a, ?_⟩
    change f 1 * algebraMap C L a = algebraMap C L a
    rw [map_one, one_mul]
  let S : IntermediateField C L := q.toRingHom.fieldRange.toIntermediateField hC
  have hF : Set.range f ⊆ S := by
    rintro _ ⟨x, rfl⟩
    refine ⟨x ⊗ₜ[k] 1, ?_⟩
    change f x * algebraMap C L 1 = f x
    rw [map_one, mul_one]
  have hS : S = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact IntermediateField.adjoin_le_iff.mpr hF
  refine ⟨q.injective, ?_⟩
  intro x
  have hx : x ∈ S := by
    rw [hS]
    trivial
  exact hx

variable {L' : Type*} [Field L'] [Algebra k L'] [Algebra C L']
    [IsScalarTower k C L']

private theorem constant_generated_field_equiv
    (f : F →ₐ[k] L) (g : F →ₐ[k] L')
    (hsc : ∀ x : F, IsSeparable k x → x ∈ (algebraMap k F).range)
    (hf : IntermediateField.adjoin C (Set.range f) = ⊤)
    (hg : IntermediateField.adjoin C (Set.range g) = ⊤) :
    ∃ e : L ≃ₐ[C] L', ∀ x : F, e (f x) = g x := by
  let q : F ⊗[k] C →ₐ[k] L :=
    Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom k C L)
      (fun _ _ => Commute.all _ _)
  let q' : F ⊗[k] C →ₐ[k] L' :=
    Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom k C L')
      (fun _ _ => Commute.all _ _)
  let e : F ⊗[k] C ≃+* L :=
    RingEquiv.ofBijective q.toRingHom
      (tensorLift_bijective_of_constant_generation f hsc hf)
  let e' : F ⊗[k] C ≃+* L' :=
    RingEquiv.ofBijective q'.toRingHom
      (tensorLift_bijective_of_constant_generation g hsc hg)
  have he (x : F) (a : C) : e (x ⊗ₜ[k] a) = f x * algebraMap C L a := rfl
  have he' (x : F) (a : C) : e' (x ⊗ₜ[k] a) = g x * algebraMap C L' a := rfl
  let E : L ≃+* L' := e.symm.trans e'
  have hconstants (a : C) : E (algebraMap C L a) = algebraMap C L' a := by
    have hleft : e (1 ⊗ₜ[k] a) = algebraMap C L a := by
      rw [he, map_one, one_mul]
    change e' (e.symm (algebraMap C L a)) = algebraMap C L' a
    rw [← hleft, e.symm_apply_apply, he', map_one, one_mul]
  refine ⟨AlgEquiv.ofRingEquiv (f := E) hconstants, ?_⟩
  intro x
  have hleft : e (x ⊗ₜ[k] 1) = f x := by
    rw [he, map_one, mul_one]
  change e' (e.symm (f x)) = g x
  rw [← hleft, e.symm_apply_apply, he', map_one, mul_one]

end TensorComparison

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve EtaleFundamentalGroups

variable {k F Ω : Type u} [Field k] [Field F] [Field Ω]
    [Algebra k F] [Algebra F Ω] [Algebra k Ω] [IsScalarTower k F Ω]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of k)) [GeometricallyIntegral c]
    (p : Spec (.of F) ⟶ X) [IsDominant p] [IsPreimmersion p]
    (hp : p ≫ c = Spec.map (CommRingCat.ofHom (algebraMap k F)))

local notation "C" => separableClosure k Ω
local notation "G" => geometricConstantExtension k F Ω
local notation "Y" => pullback c (specMap k C)

/-- The geometric extension carries its canonical constant-field algebra. -/
local instance geometricBaseChangeConstants : Algebra C G :=
  constantAlgebra (K := F) C

private local instance geometricBaseChangeConstantsTower : IsScalarTower k C G :=
  constantScalarTower (K := F) C

/-- The base-changed function field uses the scalar map from the base projection. -/
local instance geometricBaseChangeFunctionFieldConstants : Algebra C (Y).functionField :=
  (baseToFunctionField (pullback.snd c (specMap k C))).toAlgebra

private local instance geometricBaseChangeFunctionFieldGround : Algebra k (Y).functionField :=
  ((algebraMap C (Y).functionField).comp (algebraMap k C)).toAlgebra

private local instance geometricBaseChangeFunctionFieldTower :
    IsScalarTower k C (Y).functionField :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

include hp in
/-- The original base-changed scheme has the exact geometric function
field used by M1. Its constant scalar map and all original germ maps are
preserved by the constructed equivalence. -/
theorem exists_geometricConstantBaseChangeAlgEquiv :
    ∃ e : G ≃ₐ[C] (Y).functionField,
      ∀ (U : X.Opens) [Nonempty U]
        [Nonempty ((pullback.fst c (specMap k C)) ⁻¹ᵁ U)] (a : Γ(X, U)),
        e (algebraMap F G (genericFieldSourceRingEquiv p (X.germToFunctionField U a))) =
          (Y).germToFunctionField ((pullback.fst c (specMap k C)) ⁻¹ᵁ U)
            (((pullback.fst c (specMap k C)).app U).hom a) := by
  obtain ⟨φ, hφ, hgenφ⟩ := exists_functionField_constantExtension C c
  let eF := genericFieldSourceRingEquiv p
  have hsource (a : k) : eF.symm (algebraMap k F a) = baseToFunctionField c a := by
    have hcoeff :
        CommRingCat.ofHom (eF.toRingHom.comp (baseToFunctionField c)) =
          CommRingCat.ofHom (algebraMap k F) := by
      apply Spec.map_injective
      change Spec.map (CommRingCat.ofHom (baseToFunctionField c) ≫
        CommRingCat.ofHom eF.toRingHom) = _
      rw [Spec.map_comp, ← fromSpecStalk_genericPoint_comp_base c]
      have hsource : Spec.map (CommRingCat.ofHom eF.toRingHom) ≫
          X.fromSpecStalk (genericPoint X) = p :=
        genericFieldSourceIso_hom_fromSpecStalk p
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f : Spec (CommRingCat.of F) ⟶ X => f ≫ c) hsource).trans hp)
    apply eF.injective
    rw [eF.apply_symm_apply]
    exact (congrArg (fun q : CommRingCat.of k ⟶ CommRingCat.of F => q.hom a) hcoeff).symm
  let f : F →ₐ[k] (Y).functionField :=
    { toRingHom := φ.comp eF.symm.toRingHom
      commutes' := fun a => by
        change φ (eF.symm (algebraMap k F a)) =
          algebraMap C (Y).functionField (algebraMap k C a)
        rw [hsource]
        exact functionField_constantExtension_map_constants C c φ hφ a }
  have hrange : Set.range f = Set.range φ := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨eF.symm a, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨eF a, ?_⟩
      change φ (eF.symm (eF a)) = φ a
      rw [eF.symm_apply_apply]
  have hgen : IntermediateField.adjoin C (Set.range f) = ⊤ := by
    rw [hrange]
    exact hgenφ
  have hsc (x : F) (hx : IsSeparable k x) : x ∈ (algebraMap k F).range :=
    GeometricallyIntegral.genericFieldSource_fullConstants c p hp x hx.isIntegral.isAlgebraic
  obtain ⟨e, he⟩ := constant_generated_field_equiv
    (IsScalarTower.toAlgHom k F G) f hsc
    (constantExtension_adjoin_originalField (K := F) C) hgen
  refine ⟨e, ?_⟩
  intro U hU hpre a
  have h := he (eF (X.germToFunctionField U a))
  change e (algebraMap F G (eF (X.germToFunctionField U a))) =
    φ (eF.symm (eF (X.germToFunctionField U a))) at h
  rw [eF.symm_apply_apply] at h
  exact h.trans (hφ U a).symm

variable [Finite k] [IsSepClosed Ω] [IsProper c] [SmoothOfRelativeDimension 1 c]

private local instance geometricBaseChangeAlgebraicallyClosedConstants : IsAlgClosed C :=
  IsAlgClosure.isAlgClosed (R := k) (K := C)

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

include hp in
/-- A genuine proper smooth model of M1's original field is obtained from
the original compactification by constant base change. Its isomorphism with
that base change retains the original supplied generic-source coefficients.
The model's point/place and stalk data therefore refer to this same field. -/
theorem exists_geometricConstantBaseChangeCurveModel :
    ∃ M : CurveModel C G, GeometricallyIntegral M.toBase ∧
      ∃ eC : M.C ≅ Y, eC.hom ≫ pullback.snd c (specMap k C) = M.toBase ∧
        ∀ (U : X.Opens) [Nonempty U]
          [Nonempty ((eC.hom ≫ pullback.fst c (specMap k C)) ⁻¹ᵁ U)] (a : Γ(X, U)),
          M.ffEquiv.symm
              (M.C.germToFunctionField
                ((eC.hom ≫ pullback.fst c (specMap k C)) ⁻¹ᵁ U)
                (((eC.hom ≫ pullback.fst c (specMap k C)).app U).hom a)) =
            algebraMap F G (genericFieldSourceRingEquiv p (X.germToFunctionField U a)) := by
  obtain ⟨eG, hG⟩ := exists_geometricConstantBaseChangeAlgEquiv (Ω := Ω) c p hp
  obtain ⟨_, _, M₀, e₀, he₀, hM₀⟩ :=
    exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
      k c C (specMap k C)
  obtain ⟨M, e₁, he₁, hM⟩ :=
    CurveModel.exists_curveModel_iso_ffEquiv_symm_germToFunctionField_eq_of_algEquiv
      eG.symm M₀
  let eC : M.C ≅ Y := e₁.trans e₀
  have heC : eC.hom ≫ pullback.snd c (specMap k C) = M.toBase := by
    change (e₁.hom ≫ e₀.hom) ≫ pullback.snd c (specMap k C) = M.toBase
    rw [Category.assoc, he₀, he₁]
  refine ⟨M, geometricallyIntegral_of_isAlgClosed M.toBase, eC, heC, ?_⟩
  intro U hU hpre a
  let V : (Y).Opens := (pullback.fst c (specMap k C)) ⁻¹ᵁ U
  let V₀ : M₀.C.Opens := e₀.hom ⁻¹ᵁ V
  have hV : Nonempty V := by
    obtain ⟨x⟩ := hpre
    exact ⟨⟨eC.hom x.val, x.property⟩⟩
  have hV₀ : Nonempty V₀ := by
    obtain ⟨x⟩ := hpre
    exact ⟨⟨e₁.hom x.val, x.property⟩⟩
  have hV₁ : Nonempty (e₁.hom ⁻¹ᵁ V₀) := hpre
  have hm₀ := hM₀ V (((pullback.fst c (specMap k C)).app U).hom a)
  have hm := hM V₀
    ((e₀.hom.app V).hom (((pullback.fst c (specMap k C)).app U).hom a))
  have hcombined := hm.trans (congrArg eG.symm hm₀)
  have hgeometric :
      eG.symm ((Y).germToFunctionField V
        (((pullback.fst c (specMap k C)).app U).hom a)) =
        algebraMap F G (genericFieldSourceRingEquiv p (X.germToFunctionField U a)) := by
    rw [← hG U a, eG.symm_apply_apply]
  exact hcombined.trans hgeometric

end FunctionField
