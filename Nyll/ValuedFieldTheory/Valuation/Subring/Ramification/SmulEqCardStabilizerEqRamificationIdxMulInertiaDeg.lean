/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.Tactic.Ext
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Ring.Action.Field
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.IsGaloisGroup.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Nyll.ValuedFieldTheory.Valuation.Subring.Discrete.DVRAlgebraMapMemSeparable
public import Nyll.SchemeTheory.RingTheory.Localization.InertiaDegree

/-!
# Valuation Subring exists smul eq and card stabilizer eq ramification Idx mul inertia Deg
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg

namespace EmbCountGal

open IsLocalRing IsDedekindDomain
open scoped Pointwise

open ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable.EmbCountDvr
  (Over overAlgebra valuationSubringAtCenter_eq over_valuationSubringAtPrime
  mem_maximalIdeal_iff_inv_not_mem mem_of_mem_integralClosure toOver coe_toOver
  center mem_center_iff vOf liesOver_maximalIdeal ne_top_of_over
  algebraMap_overAlgebra_injective maximalIdeal_ne_bot isTorsionFree_integralClosure
  isFractionRing_integralClosure isDedekindDomain_integralClosure finite_integralClosure)

section dict2

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {F : Type*} [Field F] [Algebra K F] [Algebra C F] [IsScalarTower C K F]
variable [IsFractionRing (integralClosure C F) F] [IsDedekindDomain (integralClosure C F)]

local notation "Wv" => HeightOneSpectrum.valuationSubringAtPrime F

include K in
theorem ramificationIdx_mul_inertiaDeg_Wv (v : HeightOneSpectrum (integralClosure C F))
    (hv : ∀ c : C, algebraMap C F c ∈ Wv v) :
    letI := overAlgebra (Wv v) hv
    (maximalIdeal C).ramificationIdx' (maximalIdeal (Wv v)) *
      (maximalIdeal (Wv v)).inertiaDeg C =
    (maximalIdeal C).ramificationIdx' v.asIdeal * v.asIdeal.inertiaDeg C := by
  let _ : Algebra C (Wv v) := overAlgebra (Wv v) hv
  have _ := liesOver_maximalIdeal v
  have _ : IsScalarTower C (integralClosure C F) (Wv v) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  have _ : IsDiscreteValuationRing (Wv v) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure C F)
      v.ne_bot (Wv v)
  have hmapS : Ideal.map (algebraMap (integralClosure C F) (Wv v)) v.asIdeal =
      maximalIdeal (Wv v) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal (Wv v)
  have hmW0 : maximalIdeal (Wv v) ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  have : (maximalIdeal (Wv v)).LiesOver v.asIdeal :=
    ⟨(IsLocalization.AtPrime.under_maximalIdeal (Wv v) v.asIdeal).symm⟩
  have he : (maximalIdeal C).ramificationIdx' (maximalIdeal (Wv v)) =
      (maximalIdeal C).ramificationIdx' v.asIdeal *
        v.asIdeal.ramificationIdx' (maximalIdeal (Wv v)) :=
    Ideal.ramificationIdx'_algebra_tower (by rw [hmapS]; exact hmW0)
      (by
        rw [Ne, Ideal.map_eq_bot_iff_of_injective (algebraMap_overAlgebra_injective K _ _)]
        exact maximalIdeal_ne_bot)
      hmapS.le
  have he1 : v.asIdeal.ramificationIdx' (maximalIdeal (Wv v)) = 1 := by
    rw [← hmapS]
    exact Ideal.ramificationIdx'_map_self_eq_one
      (by rw [hmapS]; exact (maximalIdeal.isMaximal _).ne_top) (by rw [hmapS]; exact hmW0)
  have hf : (maximalIdeal (Wv v)).inertiaDeg C =
      v.asIdeal.inertiaDeg C * (maximalIdeal (Wv v)).inertiaDeg (integralClosure C F) :=
    Ideal.inertiaDeg_tower _ _
  have hf1 : (maximalIdeal (Wv v)).inertiaDeg (integralClosure C F) = 1 :=
    _root_.IsLocalization.AtPrime.inertiaDeg_maximalIdeal_eq_one v.asIdeal (Wv v)
  rw [he, he1, hf, hf1, mul_one, mul_one]

end dict2

section galois

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {M : Type*} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
variable [IsFractionRing (integralClosure C M) M] [IsDedekindDomain (integralClosure C M)]
variable [MulSemiringAction (M ≃ₐ[K] M) (integralClosure C M)]
variable [SMulDistribClass (M ≃ₐ[K] M) (integralClosure C M) M]

omit [IsDomain C] [IsDiscreteValuationRing C] [IsFractionRing C K]
    [IsFractionRing (integralClosure C M) M] [IsDedekindDomain (integralClosure C M)]
    [MulSemiringAction (M ≃ₐ[K] M) (integralClosure C M)]
    [SMulDistribClass (M ≃ₐ[K] M) (integralClosure C M) M] in
theorem smul_algebraMap (σ : M ≃ₐ[K] M) (c : C) : σ • algebraMap C M c = algebraMap C M c := by
  rw [AlgEquiv.smul_def, IsScalarTower.algebraMap_apply C K M, AlgEquiv.commutes]

theorem mem_smul_nonunits_iff (σ : M ≃ₐ[K] M) (V : ValuationSubring M) (x : M) :
    x ∈ (σ • V).nonunits ↔ σ⁻¹ • x ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'', smul_eq_zero_iff_eq]
omit [IsFractionRing C K] [IsFractionRing (integralClosure C M) M]
    [IsDedekindDomain (integralClosure C M)]
    [MulSemiringAction (M ≃ₐ[K] M) (integralClosure C M)]
    [SMulDistribClass (M ≃ₐ[K] M) (integralClosure C M) M] in
theorem over_smul (V : ValuationSubring M) (h : Over C V) (σ : M ≃ₐ[K] M) : Over C (σ • V) := by
  refine ⟨fun c => ?_, fun c => ?_⟩
  · rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_algebraMap]; exact h.mem c
  · rw [mem_smul_nonunits_iff, smul_algebraMap]; exact h.nonunit_iff c
omit [IsDomain C] [IsDiscreteValuationRing C] [Algebra C K] [IsFractionRing C K]
    [IsScalarTower C K M] [IsFractionRing (integralClosure C M) M]
    [IsDedekindDomain (integralClosure C M)] in
theorem coe_smul_integralClosure (σ : M ≃ₐ[K] M) (s : integralClosure C M) :
    ((σ • s : integralClosure C M) : M) = σ • (s : M) := by
  have h1 : ∀ t : integralClosure C M, ((t : integralClosure C M) : M) = t • (1 : M) := fun t => by
    rw [← Algebra.algebraMap_eq_smul_one]; rfl
  rw [h1, h1 s, smul_distrib_smul, smul_one]
omit [IsDomain C] [IsDiscreteValuationRing C] [Algebra C K] [IsFractionRing C K] [IsScalarTower C K
  M]
    [IsFractionRing (integralClosure C M) M] [IsDedekindDomain (integralClosure C M)] in
theorem center_smul (V : ValuationSubring M) (h : ∀ c : C, algebraMap C M c ∈ V) (σ : M ≃ₐ[K] M)
    (h' : ∀ c : C, algebraMap C M c ∈ σ • V) :
    center (σ • V) h' = σ • center V h := by
  ext s
  rw [mem_center_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_center_iff,
    mem_smul_nonunits_iff, coe_smul_integralClosure]
omit [IsDomain C] [IsDiscreteValuationRing C]
    [IsFractionRing (integralClosure C M) M] [IsDedekindDomain (integralClosure C M)] in
theorem center_congr (V₁ V₂ : ValuationSubring M) (h₁ : ∀ c : C, algebraMap C M c ∈ V₁)
    (h₂ : ∀ c : C, algebraMap C M c ∈ V₂) (hV : V₁ = V₂) : center V₁ h₁ = center V₂ h₂ := by
  subst hV; rfl

variable [FiniteDimensional K M] [IsGaloisGroup (M ≃ₐ[K] M) C (integralClosure C M)]

include K in
theorem exists_smul_eq (V V' : ValuationSubring M) (h : Over C V) (h' : Over C V') :
    ∃ σ : M ≃ₐ[K] M, σ • V' = V := by
  have _ := liesOver_maximalIdeal (vOf K V h)
  have _ := liesOver_maximalIdeal (vOf K V' h')
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (maximalIdeal C) (vOf K V' h').asIdeal
    (vOf K V h).asIdeal (M ≃ₐ[K] M)
  refine ⟨σ, ?_⟩
  have hO : Over C (σ • V') := over_smul K V' h' σ
  have hc : center (σ • V') hO.mem = center V h.mem := by
    rw [center_smul K V' h'.mem σ hO.mem]; exact hσ
  have hv : vOf K (σ • V') hO = vOf K V h := HeightOneSpectrum.ext hc
  rw [← valuationSubringAtCenter_eq K (σ • V') hO, hv, valuationSubringAtCenter_eq K V h]
omit [FiniteDimensional K M] [IsGaloisGroup (M ≃ₐ[K] M) C (integralClosure C M)] in
theorem stabilizer_eq (V : ValuationSubring M) (h : Over C V) :
    MulAction.stabilizer (M ≃ₐ[K] M) V =
      MulAction.stabilizer (M ≃ₐ[K] M) (center V h.mem) := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  have hO : Over C (σ • V) := over_smul K V h σ
  constructor
  · intro hσ
    rw [← center_smul K V h.mem σ hO.mem]
    exact center_congr _ _ _ _ hσ
  · intro hσ
    have hc : center (σ • V) hO.mem = center V h.mem := by
      rw [center_smul K V h.mem σ hO.mem]; exact hσ
    have hv : vOf K (σ • V) hO = vOf K V h := HeightOneSpectrum.ext hc
    rw [← valuationSubringAtCenter_eq K (σ • V) hO, hv, valuationSubringAtCenter_eq K V h]

variable [Module.Finite C (integralClosure C M)]

include K in
theorem card_stabilizer (V : ValuationSubring M) (h : Over C V) :
    Nat.card ↥(MulAction.stabilizer (M ≃ₐ[K] M) V) =
      (maximalIdeal C).ramificationIdx' (vOf K V h).asIdeal *
        (vOf K V h).asIdeal.inertiaDeg C := by
  have _ := liesOver_maximalIdeal (vOf K V h)
  have _ := isTorsionFree_integralClosure K (F := M) (C := C)
  rw [stabilizer_eq K V h]
  change Nat.card ↥(MulAction.stabilizer (M ≃ₐ[K] M) (vOf K V h).asIdeal) = _
  have h1 : Nat.card ↥(MulAction.orbit (M ≃ₐ[K] M) (vOf K V h).asIdeal) *
      Nat.card ↥(MulAction.stabilizer (M ≃ₐ[K] M) (vOf K V h).asIdeal) = Nat.card (M ≃ₐ[K] M) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (M ≃ₐ[K] M) (vOf K V h).asIdeal)
  rw [Algebra.IsInvariant.orbit_eq_primesOver C (integralClosure C M) (M ≃ₐ[K] M) (maximalIdeal C)
    (vOf K V h).asIdeal, Nat.card_coe_set_eq] at h1
  have h2 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (maximalIdeal C) (integralClosure C M) (M ≃ₐ[K] M)
  rw [← h1] at h2
  have h3 := mul_left_cancel₀
    (IsDedekindDomain.primesOver_ncard_ne_zero (maximalIdeal C) (integralClosure C M)) h2
  have _ := (vOf K V h).isMaximal
  rw [← h3, Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal C) (vOf K V h).asIdeal (M
    ≃ₐ[K] M),
    Ideal.inertiaDegIn_eq_inertiaDeg (maximalIdeal C) (vOf K V h).asIdeal (M ≃ₐ[K] M)]
  congr 1
  exact (Ideal.ramificationIdx'_eq_ramificationIdx (p := maximalIdeal C) (q := (vOf K V h).asIdeal)
    (maximalIdeal_ne_bot (C := C))).symm

end galois

section assembly

variable {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
variable {M : Type*} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
variable [FiniteDimensional K M] [IsGalois K M]

theorem ef_congr (V₁ V₂ : ValuationSubring M) (h₁ : ∀ c : C, algebraMap C M c ∈ V₁)
    (h₂ : ∀ c : C, algebraMap C M c ∈ V₂) (hV : V₁ = V₂) :
    (letI := overAlgebra V₁ h₁
     (maximalIdeal C).ramificationIdx' (maximalIdeal V₁) * (maximalIdeal V₁).inertiaDeg C) =
    (letI := overAlgebra V₂ h₂
     (maximalIdeal C).ramificationIdx' (maximalIdeal V₂) * (maximalIdeal V₂).inertiaDeg C) := by
  subst hV; rfl
include K in
theorem main (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ maximalIdeal C) :
    (∀ V' : ValuationSubring M, (∀ c : C, algebraMap C M c ∈ V') →
        (∀ c : C, algebraMap C M c ∈ V'.nonunits ↔ c ∈ maximalIdeal C) →
        ∃ g : M ≃ₐ[K] M, g • V' = V) ∧
    Nat.card ↥(V.decompositionSubgroup K) =
      (letI : Algebra C ↥V := ((algebraMap C M).codRestrict V hCV).toAlgebra
       (maximalIdeal C).ramificationIdx' (maximalIdeal ↥V) *
         (maximalIdeal ↥V).inertiaDeg C) := by
  have _ := isFractionRing_integralClosure K (F := M) (C := C)
  have _ := isDedekindDomain_integralClosure K (F := M) (C := C)
  have _ := finite_integralClosure K (F := M) (C := C)
  let _ : MulSemiringAction (M ≃ₐ[K] M) (integralClosure C M) :=
    IsIntegralClosure.MulSemiringAction C K M (integralClosure C M)
  have _ : IsGaloisGroup (M ≃ₐ[K] M) C (integralClosure C M) :=
    IsGaloisGroup.of_isFractionRing _ _ _ K M
  have h : Over C V := ⟨hCV, hCVmax⟩
  refine ⟨fun V' h1 h2 => exists_smul_eq K V V' h ⟨h1, h2⟩, ?_⟩
  change Nat.card ↥(MulAction.stabilizer (M ≃ₐ[K] M) V) = _
  rw [card_stabilizer K V h]
  have hv : ∀ c : C,
      algebraMap C M c ∈ HeightOneSpectrum.valuationSubringAtPrime M (vOf K V h) :=
    (over_valuationSubringAtPrime (vOf K V h)).mem
  rw [← ramificationIdx_mul_inertiaDeg_Wv K (vOf K V h) hv]
  exact ef_congr _ _ _ _ (valuationSubringAtCenter_eq K V h)

end assembly

end EmbCountGal

open IsLocalRing in
open scoped Pointwise in
theorem _root_.ValuationSubring.exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {M : Type*} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
    [FiniteDimensional K M] [IsGalois K M]
    (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ maximalIdeal C) :
    (∀ V' : ValuationSubring M, (∀ c : C, algebraMap C M c ∈ V') →
        (∀ c : C, algebraMap C M c ∈ V'.nonunits ↔ c ∈ maximalIdeal C) →
        ∃ g : M ≃ₐ[K] M, g • V' = V) ∧
    Nat.card ↥(V.decompositionSubgroup K) =
      (letI : Algebra C ↥V := ((algebraMap C M).codRestrict V hCV).toAlgebra
       (maximalIdeal C).ramificationIdx' (maximalIdeal ↥V) *
         (maximalIdeal ↥V).inertiaDeg C) :=
  EmbCountGal.main K V hCV hCVmax
end ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation
