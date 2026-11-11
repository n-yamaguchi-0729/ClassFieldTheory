/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueDVR
public import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationResidueCoefficient
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # RationalCuspDecompositionConstants -/

@[expose] public section

noncomputable section
open SchemeTheory
open scoped Pointwise
namespace EtaleFundamentalGroups.Inertia

universe u
attribute [local instance] Ideal.Quotient.field normalizationCommAlgGaloisAction

section Constants
variable (k A κ Ω : Type u)
  [Field k] [CommRing A] [IsLocalRing A] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k κ] [Algebra k Ω]
  [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower k A Ω] [IsScalarTower k κ Ω]
  [Algebra.IsAlgebraic k κ]

/-- The prescribed constant embedding, codomain-restricted by integrality. -/
def arithmeticConstantNormalizationMap : κ →+* normalizationCommAlgCat A Ω where
  toFun x := ⟨algebraMap κ Ω x,
    ((Algebra.IsIntegral.isIntegral (R := k) x).map
      (IsScalarTower.toAlgHom k κ Ω)).tower_top⟩
  map_one' := Subtype.ext (map_one (algebraMap κ Ω))
  map_zero' := Subtype.ext (map_zero (algebraMap κ Ω))
  map_add' x y := Subtype.ext (map_add (algebraMap κ Ω) x y)
  map_mul' x y := Subtype.ext (map_mul (algebraMap κ Ω) x y)

/-- Reduction of those same constants at the fixed normalization prime. -/
def arithmeticConstantResidueMap
    (Q : Ideal (normalizationCommAlgCat A Ω)) :
    κ →+* ((normalizationCommAlgCat A Ω) ⧸ Q) :=
  (Ideal.Quotient.mk Q).comp (arithmeticConstantNormalizationMap k A κ Ω)

omit [IsLocalRing A] in
private theorem arithmeticConstantNormalizationMap_base (x : k) :
    arithmeticConstantNormalizationMap k A κ Ω (algebraMap k κ x) =
      algebraMap A (normalizationCommAlgCat A Ω) (algebraMap k A x) := by
  apply Subtype.ext
  exact (IsScalarTower.algebraMap_apply k κ Ω x).symm.trans
    (IsScalarTower.algebraMap_apply k A Ω x)

/-- Rationality of the original closed point supplies the coefficient square. -/
theorem arithmeticConstantResidueMap_coefficient
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    (r : A →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal A)
    (a : A) :
    Ideal.Quotient.mk Q (algebraMap A (normalizationCommAlgCat A Ω) a) =
      arithmeticConstantResidueMap k A κ Ω Q (algebraMap k κ (r a)) := by
  have hz : a - algebraMap k A (r a) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hr]
    change r (a - algebraMap k A (r a)) = 0
    rw [map_sub, r.commutes, Algebra.algebraMap_self_apply, sub_self]
  have hunder : Q.under A = IsLocalRing.maximalIdeal A :=
    normalizationResidueBaseIdeal_eq_maximalIdeal A Ω Q
  have hmem : algebraMap A (normalizationCommAlgCat A Ω)
      (a - algebraMap k A (r a)) ∈ Q := by
    change a - algebraMap k A (r a) ∈ Q.under A
    rwa [hunder]
  have heq := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [map_sub, map_sub, sub_eq_zero] at heq
  calc
    Ideal.Quotient.mk Q (algebraMap A (normalizationCommAlgCat A Ω) a) =
        Ideal.Quotient.mk Q (algebraMap A (normalizationCommAlgCat A Ω)
          (algebraMap k A (r a))) := heq
    _ = arithmeticConstantResidueMap k A κ Ω Q (algebraMap k κ (r a)) :=
      congrArg (Ideal.Quotient.mk Q)
        (arithmeticConstantNormalizationMap_base k A κ Ω (r a)).symm

/-- The canonical constant residue map is bijective; no residue identification
is selected independently of Q or of the given constant embedding. -/
theorem arithmeticConstantResidueMap_bijective [IsAlgClosed κ]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
    (r : A →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal A) :
    Function.Bijective (arithmeticConstantResidueMap k A κ Ω Q) := by
  let E := (normalizationCommAlgCat A Ω) ⧸ Q
  let f : κ →+* E := arithmeticConstantResidueMap k A κ Ω Q
  let : Algebra κ E := f.toAlgebra
  let : Algebra.IsIntegral A (normalizationCommAlgCat A Ω) :=
    ⟨fun b => integralClosure.isIntegral (show integralClosure A Ω from b)⟩
  have : Algebra.IsIntegral A E :=
    Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ A Q)
      Ideal.Quotient.mk_surjective
  have hcomp : (algebraMap κ E).comp ((algebraMap k κ).comp r.toRingHom) =
      (RingHom.id E).comp (algebraMap A E) := by
    ext a
    exact (arithmeticConstantResidueMap_coefficient k A κ Ω Q r hr a).symm
  have : Algebra.IsIntegral κ E := ⟨fun y => by
    exact IsIntegral.map_of_comp_eq ((algebraMap k κ).comp r.toRingHom)
      (RingHom.id E) hcomp (Algebra.IsIntegral.isIntegral (R := A) y)⟩
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end Constants

section DecompositionLift
variable (k A F κ Ω : Type u)
  [Field k] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field F] [Field κ] [Field Ω]
  [Algebra k A] [Algebra k F] [Algebra k κ] [Algebra k Ω]
  [Algebra A F] [IsFractionRing A F]
  [Algebra F Ω] [Algebra A Ω] [Algebra κ Ω]
  [IsScalarTower A F Ω] [IsScalarTower k A Ω]
  [IsScalarTower k F Ω] [IsScalarTower k κ Ω]
  [IsGalois F Ω] [IsAlgClosed κ] [IsAlgClosure k κ]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]
  (r : A →ₐ[k] k) (hr : RingHom.ker r.toRingHom = IsLocalRing.maximalIdeal A)

include r hr in
/-- Every automorphism of the fixed algebraic constant closure has a lift in
this SAME normalization-prime decomposition group. -/
theorem exists_normalizationDecomposition_lift_constants (σ : κ ≃ₐ[k] κ) :
    ∃ d : normalizationDecompositionGroup A F Ω Q,
      (d.val.restrictScalars k).restrictNormal κ = σ := by
  let B := normalizationCommAlgCat A Ω
  let E := B ⧸ Q
  let c : κ →+* B := arithmeticConstantNormalizationMap k A κ Ω
  let f : κ →+* E := arithmeticConstantResidueMap k A κ Ω Q
  let e : κ ≃+* E := RingEquiv.ofBijective f
    (arithmeticConstantResidueMap_bijective k A κ Ω Q r hr)
  let τ : E ≃+* E := e.symm.trans (σ.toRingEquiv.trans e)
  let : Algebra (A ⧸ nativeAlgebraResidueBaseIdeal B Q) E :=
    Ideal.Quotient.algebraQuotientOfLEComap (p := Q.under A) (P := Q) le_rfl
  let ρ : normalizationResidueAutomorphisms A Ω Q :=
    { τ with
      commutes' := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change τ (Ideal.Quotient.mk Q (algebraMap A B a)) =
          Ideal.Quotient.mk Q (algebraMap A B a)
        rw [arithmeticConstantResidueMap_coefficient k A κ Ω Q r hr a]
        change e (σ (e.symm (e (algebraMap k κ (r a))))) =
          e (algebraMap k κ (r a))
        rw [e.symm_apply_apply, σ.commutes] }
  obtain ⟨d, hd⟩ := normalizationResidueMorphism_surjective A F Ω Q ρ
  refine ⟨d, ?_⟩
  let δ := (d.val.restrictScalars k).restrictNormal κ
  have hc (x : κ) : c (δ x) = d.val • c x := by
    apply Subtype.ext
    have haction := congrArg (fun z : B →+* Ω => z (c x))
      (normalizationCommAlg_action_comp_inclusion A F Ω d.val)
    change d.val (algebraMap κ Ω x) =
      (show integralClosure A Ω from d.val • c x).val at haction
    exact ((d.val.restrictScalars k).restrictNormal_commutes κ x).trans haction
  have hres (b : B) : Ideal.Quotient.mk Q (d.val • b) =
      τ (Ideal.Quotient.mk Q b) := by
    have hmap := originalNormalizationResidueMorphism_coefficientMap A F Ω Q d
    rw [hd, normalizationGaloisRingHom_eq_original] at hmap
    have hb := congrArg (fun z : B →+* E => z b) hmap
    dsimp only [nativeAlgebraResidueCoefficientMap,
      nativeAlgebraResidueAutomorphismRingEquiv, nativeResidueAutomorphismRingEquiv,
      RingHom.comp_apply, ρ] at hb
    exact hb.symm
  apply AlgEquiv.ext
  intro x
  apply e.injective
  change Ideal.Quotient.mk Q (c (δ x)) = Ideal.Quotient.mk Q (c (σ x))
  rw [hc, hres]
  change e (σ (e.symm (e x))) = e (σ x)
  rw [e.symm_apply_apply]

omit [IsDomain A] [IsDiscreteValuationRing A] [Q.IsMaximal] in
/-- The same chosen local decomposition element normalizes absolute inertia. -/
theorem rationalCusp_decomposition_mem_inertia_normalizer
    (d : normalizationDecompositionGroup A F Ω Q) :
    d.val ∈ Subgroup.normalizer (Q.inertia Gal(Ω/F) : Set Gal(Ω/F)) := by
  have hQ : d.val • Q = Q := d.property
  have hI : (Q.inertia Gal(Ω/F)).map (MulAut.conj d.val) =
      Q.inertia Gal(Ω/F) := by
    rw [← Ideal.inertia_smul, hQ]
  apply Subgroup.mem_set_normalizer_iff.mpr
  intro τ
  constructor
  · intro hτ
    rw [← hI]
    exact ⟨τ, hτ, rfl⟩
  · intro hτ
    rw [← hI] at hτ
    obtain ⟨s, hs, heq⟩ := hτ
    exact (MulAut.conj d.val).injective heq ▸ hs

include r hr in
/-- Rational cusp normalizer lifts every element of the fixed Galois group,
with the original normalization prime retained throughout. -/
theorem rationalCusp_exists_normalizer_lift_constants (σ : κ ≃ₐ[k] κ) :
    ∃ γ : Gal(Ω/F),
      γ ∈ Subgroup.normalizer (Q.inertia Gal(Ω/F) : Set Gal(Ω/F)) ∧
      (γ.restrictScalars k).restrictNormal κ = σ := by
  obtain ⟨d, hd⟩ := exists_normalizationDecomposition_lift_constants k A F κ Ω Q r hr σ
  exact ⟨d.val, rationalCusp_decomposition_mem_inertia_normalizer A F Ω Q d, hd⟩

end DecompositionLift
end EtaleFundamentalGroups.Inertia
