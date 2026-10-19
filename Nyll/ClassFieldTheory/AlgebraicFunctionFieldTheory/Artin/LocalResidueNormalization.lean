/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Finite.Basic
import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalSymbol
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Artin.LocalValuationNormalization
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.NormOpen
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.DecompositionResidue
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Completion.Galois
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.Curve
import Nyll.ValuedFieldTheory.Valuation.Completion.AdicCompletion
import Nyll.AlgebraicCurves.Places.Ramification.InertiaDegPos
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization

/-!
# Residue normalization at actual unramified places

The completed local Artin map acts on the original residue field through
its actual decomposition automorphism. Comparing the original and completed
integer rings identifies its order-one values with arithmetic Frobenius.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place ValuativeRel

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- At an unramified place an order-one local input acts on the original
residue field by arithmetic Frobenius. The action is obtained from the
actual completed local Artin map through the residue comparison. -/
theorem localDecompositionArtin_uniformizer_residue
    (w : Place k L) (he : w.ramificationIndex K = 1)
    (x : (w.restrict K).adicCompletionˣ)
    (hx : (IdeleGroup.localOrder (w.restrict K) x).toAdd = 1)
    (y : w.ResidueField) :
    IdeleGroup.decompositionResidueAut (K := K) w
        (localDecompositionArtin (K := K) w x) y =
      y ^ Nat.card (w.restrict K).ResidueField := by
  let : ValuativeRel (w.restrict K).adicCompletion :=
    placeCompletionValuativeRel (w.restrict K)
  let : ValuativeRel w.adicCompletion := placeCompletionValuativeRel w
  have : IsNonarchimedeanLocalField (w.restrict K).adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField (w.restrict K)
  have : IsNonarchimedeanLocalField w.adicCompletion :=
    placeCompletion_isNonarchimedeanLocalField w
  have := IdeleGroup.completionCanonical_hasExtension (K := K) w
  have : IsIntegralClosure 𝒪[w.adicCompletion] 𝒪[(w.restrict K).adicCompletion]
      w.adicCompletion := IdeleGroup.completionCanonical_isIntegralClosure (K := K) w
  have : IsNoetherian 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] :=
    IsIntegralClosure.isNoetherian 𝒪[(w.restrict K).adicCompletion]
      (w.restrict K).adicCompletion w.adicCompletion 𝒪[w.adicCompletion]
  have : Module.Finite 𝒪[(w.restrict K).adicCompletion] 𝒪[w.adicCompletion] :=
    Module.IsNoetherian.finite _ _
  have := IdeleGroup.completionCanonical_isUnramified (K := K) w he
  let eO : 𝒪[w.adicCompletion] ≃+* w.adicCompletionIntegers :=
    RingEquiv.subringCongr (IdeleGroup.completionInteger_eq w)
  let eObase : 𝒪[(w.restrict K).adicCompletion] ≃+*
      (w.restrict K).adicCompletionIntegers :=
    RingEquiv.subringCongr (IdeleGroup.completionInteger_eq (w.restrict K))
  let e0 : w.ResidueField ≃+* IsLocalRing.ResidueField w.adicCompletionIntegers :=
    IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
      L w.heightOneSpectrum
  let e0base : (w.restrict K).ResidueField ≃+*
      IsLocalRing.ResidueField (w.restrict K).adicCompletionIntegers :=
    IsDedekindDomain.HeightOneSpectrum.ResidueFieldEquivCompletionResidueField
      K (w.restrict K).heightOneSpectrum
  let e : w.ResidueField ≃+* 𝓀[w.adicCompletion] :=
    e0.trans (IsLocalRing.ResidueField.mapEquiv eO.symm)
  let ebase : (w.restrict K).ResidueField ≃+* 𝓀[(w.restrict K).adicCompletion] :=
    e0base.trans (IsLocalRing.ResidueField.mapEquiv eObase.symm)
  let incl : w.toValuationSubring →+* 𝒪[w.adicCompletion] :=
    eO.symm.toRingHom.comp (algebraMap w.toValuationSubring w.adicCompletionIntegers)
  have hincl (a : w.toValuationSubring) :
      (incl a : w.adicCompletion) = algebraMap L w.adicCompletion (a : L) := rfl
  have hres (a : w.toValuationSubring) :
      e (IsLocalRing.residue w.toValuationSubring a) =
        IsLocalRing.residue 𝒪[w.adicCompletion] (incl a) := by
    change IsLocalRing.ResidueField.mapEquiv eO.symm
      (IsLocalRing.residue w.adicCompletionIntegers
        (algebraMap w.toValuationSubring w.adicCompletionIntegers a)) = _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  let σ := localDecompositionArtin (K := K) w x
  have hσ : IdeleGroup.decompositionCompletionAut (K := K) w σ =
      LocalClassFieldTheory.abelianLocalArtinMap
        (w.restrict K).adicCompletion w.adicCompletion x⁻¹ := by
    change IdeleGroup.decompositionCompletionEquiv (K := K) w
      ((IdeleGroup.decompositionCompletionEquiv (K := K) w).symm _) = _
    exact (IdeleGroup.decompositionCompletionEquiv (K := K) w).apply_symm_apply _
  have hx' : LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
      (w.restrict K).adicCompletion (Additive.ofMul x⁻¹) = 1 := by
    rw [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_ofMul_inv,
      placeCompletion_valuationMap_eq_neg_localOrder, neg_neg, hx]
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨z, hz, hzres⟩ :=
    ClassFieldTheory.finiteAbelianLocalArtinMap_inverseUniformizer_residue_pow
      (w.restrict K).adicCompletion w.adicCompletion x⁻¹ hx' (incl a)
  have hza : z = incl (IdeleGroup.decompositionValuationEquiv w σ a) := by
    apply Subtype.ext
    calc
      (z : w.adicCompletion) =
          LocalClassFieldTheory.abelianLocalArtinMap
            (w.restrict K).adicCompletion w.adicCompletion x⁻¹ (incl a : w.adicCompletion) := hz
      _ = IdeleGroup.decompositionCompletionAut (K := K) w σ
          (algebraMap L w.adicCompletion (a : L)) := by rw [hσ, hincl]
      _ = algebraMap L w.adicCompletion (σ.val (a : L)) :=
        IdeleGroup.decompositionCompletionAut_algebraMap w σ (a : L)
      _ = (incl (IdeleGroup.decompositionValuationEquiv w σ a) : w.adicCompletion) := by
        rw [hincl, IdeleGroup.decompositionValuationEquiv_coe]
  apply e.injective
  change e (IdeleGroup.decompositionResidueAut (K := K) w σ
    (IsLocalRing.residue w.toValuationSubring a)) = _
  rw [IdeleGroup.decompositionResidueAut_residue, hres, ← hza, hzres, ← hres,
    map_pow]
  exact congrArg (fun m : ℕ => e (IsLocalRing.residue w.toValuationSubring a) ^ m)
    (Nat.card_congr ebase.toEquiv).symm

/-- At an unramified place, reduction identifies the actual decomposition
group with the Galois group of the actual residue extension. -/
theorem decompositionResidueAut_bijective_of_ramificationIndex_eq_one
    (w : Place k L) (he : w.ramificationIndex K = 1) :
    Function.Bijective (IdeleGroup.decompositionResidueAut (K := K) w) := by
  have hcurve : IsCurveOver k K := isCurveOver k K
  let v : Place k K := w.restrict K
  have hresidue : Module.Finite k v.ResidueField := IsCurveOver.finiteResidue v
  have hbaseFinite : Finite v.ResidueField := Module.finite_of_finite k
  let hbaseFintype : Fintype v.ResidueField := Fintype.ofFinite v.ResidueField
  have hextension : Module.Finite v.ResidueField w.ResidueField :=
    Module.finite_of_finrank_pos (w.inertiaDeg_pos (F := K))
  have hextensionFinite : Finite w.ResidueField := Module.finite_of_finite v.ResidueField
  let π : v.adicCompletionˣ := RestrictedProduct.DiscreteValuation.chosenLocalOrderSection
    v.adicCompletion (v.heightOneSpectrum.valuedAdicCompletion_surjective K) 1
  have hπ : (IdeleGroup.localOrder v π).toAdd = 1 :=
    RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection _ _ 1
  let σ : IdeleGroup.decompositionGroup (K := K) w := localDecompositionArtin (K := K) w π
  have hσ : IdeleGroup.decompositionResidueAut (K := K) w σ =
      FiniteField.frobeniusAlgEquivOfAlgebraic v.ResidueField w.ResidueField := by
    apply AlgEquiv.ext
    intro y
    change IdeleGroup.decompositionResidueAut (K := K) w σ y =
      y ^ Fintype.card v.ResidueField
    simpa only [Nat.card_eq_fintype_card] using
      localDecompositionArtin_uniformizer_residue (K := K) w he π hπ y
  have hsurj : Function.Surjective (IdeleGroup.decompositionResidueAut (K := K) w) := by
    intro τ
    obtain ⟨m, hm⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow v.ResidueField w.ResidueField).2 τ
    refine ⟨σ ^ m.val, ?_⟩
    rw [map_pow, hσ]
    exact hm
  have hcard : Nat.card (IdeleGroup.decompositionGroup (K := K) w) =
      Nat.card Gal(w.ResidueField/v.ResidueField) := by
    rw [IdeleGroup.decompositionGroup_card_eq_ramificationIndex_mul_inertiaDeg,
      he, one_mul, IsGalois.card_aut_eq_finrank]
    rfl
  exact hsurj.bijective_of_nat_card_le hcard.le

end FunctionField
