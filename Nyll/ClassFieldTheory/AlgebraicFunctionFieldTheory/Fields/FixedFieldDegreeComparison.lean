/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.SeparableDegree
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.DenseEmbedding
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FixedFieldFrobenius
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport
import Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore

/-!
# Intrinsic and ambient constant degrees of finite fixed fields

Conjugation between the two actual separable closures transports algebraic
constants. Natural degrees therefore agree by their arithmetic constant
action. The degree map is open, so the density of natural numbers in the
profinite integers extends this equality to every profinite degree.

The function-field presentation of the fixed field is shared with the caller.
No degree comparison or Frobenius compatibility is an input.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology
open scoped Topology

variable (k K : Type) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra k (SeparableClosure K)]
    [IsScalarTower k K (SeparableClosure K)]
    (H : FiniteAbstractField Gal(SeparableClosure K/K))

variable [Algebra (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [IsScalarTower k (RatFunc k) (abstractFixedField K (SeparableClosure K) H.field)]
    [FunctionField k (abstractFixedField K (SeparableClosure K) H.field)]

private theorem intrinsicFullConstantDegree_nat_ambientFixedField :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (σ : (intrinsicAbstractBase F).toSubgroup) (n : ℕ),
      (fullConstantDegreeData k F (SeparableClosure F)).degree σ.val =
          Multiplicative.ofAdd (n : ZHat) →
        (fullConstantDegreeData k K (SeparableClosure K)).normalizedDegree
          (H.toFiniteResidueAbstractField
            (fullConstantDegreeData k K (SeparableClosure K)))
          (intrinsicBaseEquivAmbientFixedField K H e σ) =
            Multiplicative.ofAdd (n : ZHat) := by
  intro F aF e σ n hσ
  have hkFΩ : IsScalarTower k F (SeparableClosure K) :=
    IsScalarTower.to₁₃₄ k K F (SeparableClosure K)
  have hkCFΩ : IsScalarTower k (algebraicClosure k F) (SeparableClosure K) :=
    IsScalarTower.to₁₂₄ k (algebraicClosure k F) F (SeparableClosure K)
  have hFft : Algebra.EssFiniteType k F := essFiniteType k F
  have hCfinite : Finite (algebraicClosure k F) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k F
  have hconstants :
      ∀ c : separableClosure (algebraicClosure k F) (SeparableClosure F),
        σ.val (c : SeparableClosure F) =
          (c : SeparableClosure F) ^ (Nat.card (algebraicClosure k F) ^ n) :=
    (absoluteConstantDegree_eq_nat_iff (algebraicClosure k F) F
      (SeparableClosure F) σ.val n).mp hσ
  apply (fixedFieldNormalizedDegree_eq_nat_iff k K (SeparableClosure K) H
    (intrinsicBaseEquivAmbientFixedField K H e σ) n).mpr
  intro c
  have hc : IsSeparable (algebraicClosure k K) (c : SeparableClosure K) :=
    mem_separableClosure_iff.mp c.property
  have hck : IsSeparable k (c : SeparableClosure K) :=
    IsSeparable.of_algebra_isSeparable_of_isSeparable k hc
  have hcF : IsSeparable (algebraicClosure k F) (c : SeparableClosure K) :=
    hck.tower_top (algebraicClosure k F)
  have hpre : IsSeparable (algebraicClosure k F) (e.symm (c : SeparableClosure K)) :=
    ((e.symm.restrictScalars (algebraicClosure k F)).isSeparable_iff).mpr hcF
  let d : separableClosure (algebraicClosure k F) (SeparableClosure F) :=
    ⟨e.symm (c : SeparableClosure K), mem_separableClosure_iff.mpr hpre⟩
  have hpow := congrArg e (hconstants d)
  rw [map_pow, e.apply_symm_apply] at hpow
  have hconj :
      (intrinsicBaseEquivAmbientFixedField K H e σ).val (c : SeparableClosure K) =
        e (σ.val (e.symm (c : SeparableClosure K))) := by
    have h := congrArg
      (fun ρ : Gal(SeparableClosure K/F) => ρ (c : SeparableClosure K))
      ((abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H.field).apply_symm_apply
        (AlgEquiv.autCongr e σ.val))
    exact h
  exact hconj.trans hpow

/-- The intrinsic full-constant degree of a finite fixed field agrees with the
normalized ambient degree under the actual separable-closure equivalence. -/
theorem intrinsicFullConstantDegree_eq_ambientFixedField :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let _ : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (τ : (intrinsicAbstractBase F).toSubgroup),
      (fullConstantDegreeData k F (SeparableClosure F)).degree τ.val =
        (fullConstantDegreeData k K (SeparableClosure K)).normalizedDegree
          (H.toFiniteResidueAbstractField
            (fullConstantDegreeData k K (SeparableClosure K)))
          (intrinsicBaseEquivAmbientFixedField K H e τ) := by
  intro F aF e τ
  have hcompact : CompactSpace (intrinsicAbstractBase F).toSubgroup :=
    isCompact_iff_compactSpace.mp (intrinsicAbstractBase F).isClosed'.isCompact
  have hsigma : SigmaCompactSpace (intrinsicAbstractBase F).toSubgroup :=
    CompactSpace.sigmaCompact
  let DF := fullConstantDegreeData k F (SeparableClosure F)
  let DK := fullConstantDegreeData k K (SeparableClosure K)
  let HR := H.toFiniteResidueAbstractField DK
  let ψ := intrinsicBaseEquivAmbientFixedField K H e
  let f : (intrinsicAbstractBase F).toSubgroup →ₜ* ZHatMul :=
    { toMonoidHom := DF.degree.toMonoidHom.comp (intrinsicAbstractBase F).toSubgroup.subtype
      continuous_toFun := DF.degree.continuous_toFun.comp continuous_subtype_val }
  let g : (intrinsicAbstractBase F).toSubgroup →ₜ* ZHatMul :=
    { toMonoidHom := (DK.normalizedDegree HR).toMonoidHom.comp ψ.toMonoidHom
      continuous_toFun := (DK.normalizedDegree HR).continuous_toFun.comp
        (intrinsicBaseEquivAmbientFixedField_continuous K H e) }
  have hnat (σ : (intrinsicAbstractBase F).toSubgroup) (n : ℕ)
      (hσ : f σ = Multiplicative.ofAdd (n : ZHat)) :
      g σ = Multiplicative.ofAdd (n : ZHat) :=
    intrinsicFullConstantDegree_nat_ambientFixedField k K H e σ n hσ
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨σ, hσ⟩ := DF.degree_surjective z
    refine ⟨(intrinsicAbstractBaseEquivAbsolute F).symm σ, ?_⟩
    change DF.degree (((intrinsicAbstractBaseEquivAbsolute F).symm σ).val) = z
    rw [intrinsicAbstractBaseEquivAbsolute_symm_apply_val]
    exact hσ
  have hopen : IsOpenMap f :=
    f.toMonoidHom.isOpenMap_of_sigmaCompact hf f.continuous_toFun
  have hint : DenseRange
      (fun z : ℤ => (Multiplicative.ofAdd (1 : ZHat)) ^ z) := by
    have hcast : DenseRange (fun z : ℤ => Multiplicative.ofAdd (z : ZHat)) :=
      (show Function.Surjective (Multiplicative.ofAdd : ZHat → ZHatMul) from
        fun z => ⟨z.toAdd, rfl⟩).denseRange.comp
        denseRange_intCast_zHat continuous_id
    convert hcast using 1
    funext z
    apply Multiplicative.ext
    change z • (1 : ZHat) = (z : ZHat)
    rw [zsmul_eq_mul, mul_one]
  have hnatural : DenseRange
      (fun n : ℕ => (Multiplicative.ofAdd (1 : ZHat)) ^ n) :=
    denseRange_zpow_iff_pow.mp hint
  have hdense : Dense
      (f ⁻¹' Set.range (fun n : ℕ => (Multiplicative.ofAdd (1 : ZHat)) ^ n)) :=
    hnatural.preimage hopen
  have heq : (f : (intrinsicAbstractBase F).toSubgroup → ZHatMul) = g :=
    hdense.denseRange_val.equalizer f.continuous_toFun g.continuous_toFun (by
      funext σ
      have hmem : ∃ n : ℕ, (Multiplicative.ofAdd (1 : ZHat)) ^ n = f σ.val :=
        σ.property
      obtain ⟨n, hn⟩ := hmem
      have hpow : (Multiplicative.ofAdd (1 : ZHat)) ^ n =
          Multiplicative.ofAdd (n : ZHat) := by
        apply Multiplicative.ext
        change n • (1 : ZHat) = (n : ZHat)
        rw [nsmul_eq_mul, mul_one]
      have hσ : f σ.val = Multiplicative.ofAdd (n : ZHat) :=
        hn.symm.trans hpow
      exact hσ.trans (hnat σ.val n hσ).symm)
  exact congrFun heq τ

end FunctionField
