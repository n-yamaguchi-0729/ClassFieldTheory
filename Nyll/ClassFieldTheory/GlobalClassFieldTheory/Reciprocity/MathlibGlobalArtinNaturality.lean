/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibTopologicalGlobalReciprocity
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinBaseEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MaximalAbelianBaseEquiv

/-!
# Finite projections and model independence of the public global Artin map

The existing Small-transported map is retained. Native reciprocity and its
pointwise naturality identify that same map with native reciprocity on the
original carrier, so every actual finite projection has its original value.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

open ClassFieldTheory

universe u v w

variable {K : Type u} {M : Type v} [Field K] [NumberField K] [Field M] [NumberField M]

/-- The actual ordinary idèle-class base equivalence, expressed in Mathlib's
idèle-class carriers through the existing topology comparisons. -/
noncomputable def mathlibIdeleClassCongr (e : K ≃ₐ[ℚ] M) :
    NumberField.IdeleClassGroup (𝓞 K) K ≃ₜ* NumberField.IdeleClassGroup (𝓞 M) M :=
  (IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm.trans
    ((ideleClassCongrContinuousMulEquiv e).trans
      (IdeleGroup.ideleClassGroupContinuousMulEquivMathlib M))

/-- Native quotient reciprocity retains the actual maximal-abelian Artin
value on the corresponding ordinary idèle class. -/
theorem mathlibIdeleClassConnectedQuotientEquivAbelianization_value
    (a : NumberField.IdeleClassGroup (𝓞 K) K) :
    mathlibAbelianizationToMaximal K
        (mathlibIdeleClassConnectedQuotientEquivAbelianization K
          (QuotientGroup.mk'
            (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)) a)) =
      maximalAbelianGlobalArtin K
        ((IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm a) := by
  let t := IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K
  let q := connectedComponentQuotientCongr t
  let mk := QuotientGroup.mk'
    (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K))
  have hq : q.symm (mk a) =
      QuotientGroup.mk' (ideleClassIdentityComponent K) (t.symm a) := by
    apply q.injective
    exact (q.apply_symm_apply (mk a)).trans
      ((congrArg mk (t.apply_symm_apply a).symm).trans
        (connectedComponentQuotientCongr_mk t (t.symm a)).symm)
  let e := absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K
  let b := absoluteGaloisGroupAbelianizationEquivSeparable K
  let f := ideleClassComponentQuotientEquivMaximalAbelianGalois K
  let g := f (q.symm (mk a))
  change e (b (b.symm (e.symm g))) = maximalAbelianGlobalArtin K (t.symm a)
  calc
    _ = e (e.symm g) := congrArg e (b.apply_symm_apply _)
    _ = g := e.apply_symm_apply g
    _ = _ := (congrArg f hq).trans (ideleClassComponentQuotientEquivMaximalAbelianGalois_mk K _)

/-- Native global reciprocity commutes pointwise with the given base-field
isomorphism and its actual absolute Galois map. -/
theorem mathlibIdeleClassConnectedQuotientEquivAbelianization_natural_mk
    (e : K ≃ₐ[ℚ] M) (a : NumberField.IdeleClassGroup (𝓞 K) K) :
    absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv
        (mathlibIdeleClassConnectedQuotientEquivAbelianization K
          (QuotientGroup.mk'
            (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)) a)) =
      mathlibIdeleClassConnectedQuotientEquivAbelianization M
        (QuotientGroup.mk'
          (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 M) M))
          (mathlibIdeleClassCongr e a)) := by
  apply (mathlibAbelianizationToMaximal M).injective
  rw [mathlibAbelianizationToMaximal_baseEquiv,
    mathlibIdeleClassConnectedQuotientEquivAbelianization_value,
    mathlibIdeleClassConnectedQuotientEquivAbelianization_value]
  let tK := IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K
  let tM := IdeleGroup.ideleClassGroupContinuousMulEquivMathlib M
  have h := infiniteGlobalIdeleClassArtinMonoidHom_semilinear
    (Ω := maximalAbelianExtension K) (Ψ := maximalAbelianExtension M)
    e (maximalAbelianExtensionBaseEquiv e.toRingEquiv)
    (maximalAbelianExtensionBaseEquiv_commutes e.toRingEquiv) (tK.symm a)
  have hclass : tM.symm (mathlibIdeleClassCongr e a) = ideleClassCongr e (tK.symm a) :=
    tM.symm_apply_apply _
  exact h.trans (congrArg (maximalAbelianGlobalArtin M) hclass.symm)

/-- Naturality holds on the connected-component quotient itself. -/
theorem mathlibIdeleClassConnectedQuotientEquivAbelianization_natural
    (e : K ≃ₐ[ℚ] M) (a : IdeleClassConnectedQuotient K) :
    absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv
        (mathlibIdeleClassConnectedQuotientEquivAbelianization K a) =
      mathlibIdeleClassConnectedQuotientEquivAbelianization M
        (connectedComponentQuotientCongr (mathlibIdeleClassCongr e) a) := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)) a
  rw [connectedComponentQuotientCongr_mk]
  exact mathlibIdeleClassConnectedQuotientEquivAbelianization_natural_mk e b

/-- The already specified Small transport is the native reciprocity map on
the original carrier. This is an equality of the existing maps. -/
theorem mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse_eq_native :
    mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse K =
      mathlibIdeleClassConnectedQuotientEquivAbelianization K := by
  let : Small.{0} K := numberField_small K
  let S := Shrink.{0} K
  let : NumberField S := numberField_shrink K
  let e : S ≃ₐ[ℚ] K := (Shrink.ringEquiv K).toRatAlgEquiv
  let q := connectedComponentQuotientCongr (mathlibIdeleClassCongr e)
  apply ContinuousMulEquiv.ext
  intro a
  change absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv
      (mathlibIdeleClassConnectedQuotientEquivAbelianization S (q.symm a)) = _
  rw [mathlibIdeleClassConnectedQuotientEquivAbelianization_natural,
    q.apply_symm_apply]

/-- Every equivalent number-field model gives the same specified public
reciprocity map, including every Small representative and its chosen closure. -/
theorem mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse_model
    (e : M ≃ₐ[ℚ] K) :
    mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse K =
      (connectedComponentQuotientCongr (mathlibIdeleClassCongr e)).symm.trans
        ((mathlibIdeleClassConnectedQuotientEquivAbelianization M).trans
          (absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv)) := by
  rw [mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse_eq_native]
  apply ContinuousMulEquiv.ext
  intro a
  change mathlibIdeleClassConnectedQuotientEquivAbelianization K a =
    absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv
      (mathlibIdeleClassConnectedQuotientEquivAbelianization M
        ((connectedComponentQuotientCongr (mathlibIdeleClassCongr e)).symm a))
  rw [mathlibIdeleClassConnectedQuotientEquivAbelianization_natural,
    ContinuousMulEquiv.apply_symm_apply]

/-- The model comparison is independent of the chosen compatible algebraic
closure equivalence as well as of the chosen equivalent base field. -/
theorem mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse_model_of_closure
    (e : M ≃ₐ[ℚ] K) (c : AlgebraicClosure M ≃+* AlgebraicClosure K)
    (hc : ∀ a : M, c (algebraMap M (AlgebraicClosure M) a) =
      algebraMap K (AlgebraicClosure K) (e a)) :
    mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse K =
      (connectedComponentQuotientCongr (mathlibIdeleClassCongr e)).symm.trans
        ((mathlibIdeleClassConnectedQuotientEquivAbelianization M).trans
          (LocalClassFieldTheory.topologicalAbelianizationCongr
            (semilinearGaloisContinuousEquiv e.toRingEquiv c hc))) := by
  have hg : LocalClassFieldTheory.topologicalAbelianizationCongr
      (semilinearGaloisContinuousEquiv e.toRingEquiv c hc) =
      absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv :=
    semilinearGaloisAbelianizationEquiv_independent e.toRingEquiv c
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure M) (AlgebraicClosure K) e.toRingEquiv)
      hc (IsAlgClosure.equivOfEquiv_algebraMap
        (AlgebraicClosure M) (AlgebraicClosure K) e.toRingEquiv)
  exact (mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse_model e).trans
    (congrArg (fun g => (connectedComponentQuotientCongr (mathlibIdeleClassCongr e)).symm.trans
      ((mathlibIdeleClassConnectedQuotientEquivAbelianization M).trans g)) hg.symm)

/-- The named public map has the original maximal-abelian value on each
ordinary class, with its original geometric normalization unchanged. -/
theorem mathlibGlobalArtin_toMaximal (a : NumberField.IdeleClassGroup (𝓞 K) K) :
    mathlibAbelianizationToMaximal K (mathlibGlobalArtin K a) =
      maximalAbelianGlobalArtin K
        ((IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm a) := by
  rw [mathlibGlobalArtin_apply,
    mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse_eq_native]
  exact mathlibIdeleClassConnectedQuotientEquivAbelianization_value a

/-- Every actual finite Galois restriction of the named public Artin map is
the original finite Artin map on the same idèle class. -/
theorem mathlibGlobalArtin_finiteProjection
    (a : NumberField.IdeleClassGroup (𝓞 K) K)
    (E : FiniteGaloisIntermediateField K (maximalAbelianExtension K)) :
    let : NumberField E := NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom E
        (mathlibAbelianizationToMaximal K (mathlibGlobalArtin K a)) =
      globalIdeleClassArtinMonoidHom (K := K) (L := E)
        ((IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm a) := by
  intro numberFieldE
  rw [mathlibGlobalArtin_toMaximal]
  exact infiniteGlobalIdeleClassArtinMonoidHom_finiteProjection
    ((IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm a) E

/-- The same finite-projection value holds for any finite abelian extension
supplied through its actual embedding in the maximal abelian extension. -/
theorem mathlibGlobalArtin_finiteProjection_of_scalarTower
    (L : Type w) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    [Algebra L (maximalAbelianExtension K)] [IsScalarTower K L (maximalAbelianExtension K)]
    (a : NumberField.IdeleClassGroup (𝓞 K) K) :
    AlgEquiv.restrictNormalHom L
        (mathlibAbelianizationToMaximal K (mathlibGlobalArtin K a)) =
      globalIdeleClassArtinMonoidHom (K := K) (L := L)
        ((IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm a) := by
  rw [mathlibGlobalArtin_toMaximal]
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (IdeleGroup.principalSubgroup K)
    ((IdeleGroup.ideleClassGroupContinuousMulEquivMathlib K).symm a)
  rw [← hb, maximalAbelianGlobalArtin_mk, globalIdeleClassArtinMonoidHom_mk]
  exact restrictNormalHom_infiniteGlobalArtinMonoidHom_of_scalarTower
    K L (maximalAbelianExtension K) b

/-- Base-field equivalences intertwine the named public Artin maps on each
idèle class. -/
theorem mathlibGlobalArtin_baseEquiv
    (e : K ≃ₐ[ℚ] M) (a : NumberField.IdeleClassGroup (𝓞 K) K) :
    absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv
        (mathlibGlobalArtin K a) =
      mathlibGlobalArtin M (mathlibIdeleClassCongr e a) := by
  rw [mathlibGlobalArtin_apply, mathlibGlobalArtin_apply,
    mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse_eq_native,
    mathlibIdeleClassConnectedQuotientEquivAbelianizationUniverse_eq_native]
  exact mathlibIdeleClassConnectedQuotientEquivAbelianization_natural_mk e a

end GlobalClassFieldTheory.Reciprocity
