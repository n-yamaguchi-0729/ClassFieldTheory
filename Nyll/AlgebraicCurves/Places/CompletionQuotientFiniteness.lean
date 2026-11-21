/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_tateAgreement.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Earlier source notices recorded for the cited upstream material:
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri
https://github.com/ImperialCollegeLondon/FLT/blob/a7dbce8494c29858093974a612a72b6454fc5cba/FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Authors: Salvatore Mercuri, Kevin Buzzard
https://github.com/ImperialCollegeLondon/FLT/blob/a7dbce8494c29858093974a612a72b6454fc5cba/FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Lean.Elab.Tactic.NormCast
public import Lean.Elab.Tactic.Omega
public import Nyll.AlgebraicCurves.Places.Basic
public import Nyll.AlgebraicCurves.Places.Completion
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.Ring.RingNF

/-!
# Finite-dimensional quotients of completed valuation rings

The actual submodule of multiples of a power is compared with the ideal quotient over the
original constant field. Finiteness for the first power then gives finiteness for every power.
The residue hypothesis here is module finiteness over the constant field, not finite cardinality.
-/

@[expose] public section

noncomputable section

namespace AlgebraicCurve.Place.CompletionQuotients

section FiniteDimensionality

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

/-- The original constant-field submodule of multiples of the given power. -/
def piPowKSubmodule (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule K u.adicCompletionIntegers where
  carrier := {y | ∃ x : u.adicCompletionIntegers, y = πh^M * x}
  add_mem' := by rintro a b ⟨xa, rfl⟩ ⟨xb, rfl⟩; exact ⟨xa + xb, by ring⟩
  zero_mem' := ⟨0, by ring⟩
  smul_mem' c y := by
    rintro ⟨x, rfl⟩
    exact ⟨c • x, by rw [Algebra.smul_def, Algebra.smul_def, mul_left_comm]⟩

variable (K L) in
/-- All power quotients are finite-dimensional at every place with finite residue over K. -/
def QuotientPowersFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (M : ℕ),
    FiniteDimensional K (u.adicCompletionIntegers ⧸ piPowKSubmodule u πh M)

/-- The multiples submodule is the principal ideal with its original scalars restricted. -/
theorem piPowKSubmodule_eq_restrictScalars (πh : u.adicCompletionIntegers) (M : ℕ) :
    piPowKSubmodule u πh M
      = (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K := by
  ext y
  rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
  exact ⟨fun ⟨x, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, h⟩⟩

/-- The actual submodule and ideal quotients agree K-linearly, using the same scalar action. -/
def quotientPiPowLinearEquivIdealQuotient (πh : u.adicCompletionIntegers) (M : ℕ) :
    (u.adicCompletionIntegers ⧸ piPowKSubmodule u πh M)
      ≃ₗ[K] (u.adicCompletionIntegers ⧸ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)) :=
  (Submodule.quotEquivOfEq _ _ (piPowKSubmodule_eq_restrictScalars u πh M)).trans
    (Submodule.Quotient.restrictScalarsEquiv K _)

variable (K L) in
/-- The first quotient is finite-dimensional at every place with finite residue over K. -/
def CotangentQuotientFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh),
    FiniteDimensional K
      (u.adicCompletionIntegers ⧸ (Ideal.span {πh} : Ideal u.adicCompletionIntegers))

/-- Multiplication has the principal ideal as its image with the original K-scalar action. -/
theorem range_mulLeft_eq_restrictScalars_span (a : u.adicCompletionIntegers) :
    LinearMap.range (LinearMap.mulLeft K a)
      = (Ideal.span {a} : Ideal u.adicCompletionIntegers).restrictScalars K := by
  ext y
  simp only [LinearMap.mem_range, LinearMap.mulLeft_apply, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩, fun ⟨x, hx⟩ => ⟨x, hx.symm⟩⟩

/-- Induction on the power gives finite-dimensionality of the actual submodule quotient. -/
theorem finiteDimensional_restrictScalarsQuot_pow [u.FiniteResidue]
    (hCot : CotangentQuotientFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K (u.adicCompletionIntegers ⧸
      (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K) := by
  induction M with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one, Submodule.restrictScalars_top]
    infer_instance
  | succ M ih =>
    have hle : (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers)
        ≤ Ideal.span {πh^M} := by
      rw [Ideal.span_singleton_le_span_singleton, pow_succ]; exact ⟨πh, rfl⟩
    have hle' : (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K
        ≤ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K :=
      Submodule.restrictScalars_mono K hle
    set N : Submodule K (u.adicCompletionIntegers ⧸
        (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K) :=
      (Submodule.restrictScalars K (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)).map
        (Submodule.restrictScalars K (Ideal.span {πh^(M+1)} : Ideal _)).mkQ with hN_def
    have hquot : FiniteDimensional K
        ((u.adicCompletionIntegers ⧸
          (Ideal.span {πh^(M+1)} : Ideal _).restrictScalars K) ⧸ N) := by
      have := ih
      exact Module.Finite.equiv
        (Submodule.quotientQuotientEquivQuotient _ _ hle').symm
    have hN : FiniteDimensional K N := by
      set φ : u.adicCompletionIntegers →ₗ[K] (u.adicCompletionIntegers ⧸
          (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K) :=
        (Submodule.restrictScalars K
            (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers)).mkQ ∘ₗ
          LinearMap.mulLeft K (πh^M) with hφ_def
      have hrange : LinearMap.range φ = N := by
        rw [hφ_def, LinearMap.range_comp, range_mulLeft_eq_restrictScalars_span, hN_def]
      have hker : LinearMap.ker φ
          = (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K := by
        simp only [hφ_def, LinearMap.ker_comp, Submodule.ker_mkQ]
        ext x
        simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.restrictScalars_mem,
          Ideal.mem_span_singleton]
        have hπM : (πh : u.adicCompletionIntegers)^M ≠ 0 := pow_ne_zero M hπh.ne_zero
        constructor
        · rintro ⟨c, hc⟩
          exact ⟨c, mul_left_cancel₀ hπM (by rw [hc, pow_succ, mul_assoc])⟩
        · rintro ⟨c, hc⟩
          exact ⟨c, by rw [hc, pow_succ, mul_assoc]⟩
      let e₁ : (u.adicCompletionIntegers ⧸
            (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K)
          ≃ₗ[K] (u.adicCompletionIntegers ⧸ LinearMap.ker φ) :=
        Submodule.quotEquivOfEq _ _ hker.symm
      let e₂ : (u.adicCompletionIntegers ⧸ LinearMap.ker φ) ≃ₗ[K] LinearMap.range φ :=
        φ.quotKerEquivRange
      let e₃ : (LinearMap.range φ : Submodule K _) ≃ₗ[K] N := LinearEquiv.ofEq _ _ hrange
      have hCK : FiniteDimensional K (u.adicCompletionIntegers ⧸
          (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K) := by
        have := hCot u πh hπh
        exact Module.Finite.equiv
          (Submodule.Quotient.restrictScalarsEquiv K
            (Ideal.span {πh} : Ideal u.adicCompletionIntegers)).symm
      exact Module.Finite.equiv ((e₁.trans e₂).trans e₃)
    exact Module.Finite.of_submodule_quotient N

/-- The same induction gives finite-dimensionality of the corresponding ideal quotient. -/
theorem finiteDimensional_idealQuot_pow [u.FiniteResidue]
    (hCot : CotangentQuotientFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K
      (u.adicCompletionIntegers ⧸ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)) := by
  have := finiteDimensional_restrictScalarsQuot_pow u hCot πh hπh M
  exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv K _)

/-- Finiteness of each first quotient supplies finiteness of all powers at the same places. -/
theorem quotientPowersFinite_of_cotangent
    (hCot : CotangentQuotientFinite K L) :
    QuotientPowersFinite K L := by
  intro u _ πh hπh M
  have := finiteDimensional_idealQuot_pow u hCot πh hπh M
  exact Module.Finite.equiv (quotientPiPowLinearEquivIdealQuotient u πh M).symm

/-- The completion integers viewed as a submodule over the base field. -/
def adicIntegersKSubmod : Submodule K u.adicCompletion where
  carrier := u.adicCompletionIntegers
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c x hx := by
    rw [Algebra.smul_def]
    exact mul_mem (by
      rw [IsScalarTower.algebraMap_apply K L u.adicCompletion]
      exact (algebraMap_mem_adicCompletionIntegers_iff u _).mpr
        (u.algebraMap_mem' c)) hx

theorem mem_adicIntegersKSubmod_iff (x : u.adicCompletion) :
    x ∈ adicIntegersKSubmod u ↔ x ∈ u.adicCompletionIntegers := Iff.rfl

/-- The space of completion elements with poles bounded by the given uniformizer power. -/
def poleWindowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule K u.adicCompletion where
  carrier := {x | (πh : u.adicCompletion)^M * x ∈ u.adicCompletionIntegers}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, mul_add] at ha hb ⊢; exact add_mem ha hb
  zero_mem' := by simp only [Set.mem_ofPred_eq, mul_zero]; exact zero_mem _
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply K L u.adicCompletion, mul_left_comm]
    exact mul_mem ((algebraMap_mem_adicCompletionIntegers_iff u _).mpr
      (u.algebraMap_mem' c)) hx

theorem mem_poleWindowKSubmod_iff (πh : u.adicCompletionIntegers) (M : ℕ)
    (x : u.adicCompletion) :
    x ∈ poleWindowKSubmod u πh M ↔ (πh : u.adicCompletion)^M * x ∈ u.adicCompletionIntegers :=
  Iff.rfl

theorem adicIntegersKSubmod_le_poleWindowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    adicIntegersKSubmod u ≤ poleWindowKSubmod u πh M :=
  fun _ hx => mul_mem (pow_mem πh.2 M) hx

variable (K L) in
/-- Finite dimensionality of each bounded pole space modulo integral completion elements. -/
def PoleWindowFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (M : ℕ),
    FiniteDimensional K
      (poleWindowKSubmod u πh M ⧸
        (adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)

theorem coe_smul_K (c : K) (x : u.adicCompletionIntegers) :
    ((c • x : u.adicCompletionIntegers) : u.adicCompletion) = c • (x : u.adicCompletion) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

/-- The linear map clearing a bounded pole by the specified uniformizer power. -/
def poleWindowShift (πh : u.adicCompletionIntegers) (M : ℕ) :
    poleWindowKSubmod u πh M →ₗ[K] u.adicCompletionIntegers where
  toFun x := ⟨(πh : u.adicCompletion)^M * (x : u.adicCompletion), x.2⟩
  map_add' x y := by apply Subtype.ext; push_cast; ring
  map_smul' c x := by
    apply Subtype.ext
    rw [coe_smul_K]
    change (πh : u.adicCompletion)^M * (c • (x : u.adicCompletion))
        = c • ((πh : u.adicCompletion)^M * (x : u.adicCompletion))
    rw [mul_smul_comm]

theorem poleWindowShift_injective (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (M : ℕ) : Function.Injective (poleWindowShift u πh M) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hπhM0 : (πh : u.adicCompletion)^M ≠ 0 := by
    refine pow_ne_zero M ?_
    intro hz
    exact hπh.ne_zero (Subtype.ext hz)
  have hx0 : (x : u.adicCompletion) = 0 := by
    have := congrArg Subtype.val hx
    push_cast at this
    exact (mul_eq_zero.mp this).resolve_left hπhM0
  exact Subtype.ext hx0

theorem poleWindowShift_surjective (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (M : ℕ) : Function.Surjective (poleWindowShift u πh M) := by
  intro y
  have hπhM0 : (πh : u.adicCompletion)^M ≠ 0 := by
    refine pow_ne_zero M ?_
    intro hz; exact hπh.ne_zero (Subtype.ext hz)
  refine ⟨⟨(y : u.adicCompletion) / (πh : u.adicCompletion)^M, ?_⟩, ?_⟩
  · rw [mem_poleWindowKSubmod_iff, mul_div_cancel₀ _ hπhM0]; exact y.2
  · apply Subtype.ext
    change (πh : u.adicCompletion)^M * ((y : u.adicCompletion) / (πh : u.adicCompletion)^M)
        = (y : u.adicCompletion)
    rw [mul_div_cancel₀ _ hπhM0]

/-- The linear equivalence obtained by clearing a bounded pole. -/
def poleWindowShiftEquiv (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    poleWindowKSubmod u πh M ≃ₗ[K] u.adicCompletionIntegers :=
  LinearEquiv.ofBijective (poleWindowShift u πh M)
    ⟨poleWindowShift_injective u πh hπh M, poleWindowShift_surjective u πh hπh M⟩

theorem poleWindowShift_image_integers (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule.map (poleWindowShift u πh M)
        ((adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)
      = piPowKSubmodule u πh M := by
  ext y
  constructor
  · rintro ⟨⟨x, hxP⟩, hxA, rfl⟩
    refine ⟨⟨(x : u.adicCompletion), hxA⟩, ?_⟩
    apply Subtype.ext; push_cast; rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨(x : u.adicCompletion),
      adicIntegersKSubmod_le_poleWindowKSubmod u πh M x.2⟩, x.2, ?_⟩
    apply Subtype.ext; push_cast; rfl

theorem poleWindowFinite_of_quotientPowersFinite
    (hDVR : QuotientPowersFinite K L) :
    PoleWindowFinite K L := by
  intro u _ πh hπh M
  have := hDVR u πh hπh M
  let e' := Submodule.Quotient.equiv
    ((adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)
    (piPowKSubmodule u πh M)
    (poleWindowShiftEquiv u πh hπh M)
    (poleWindowShift_image_integers u πh M)
  exact FiniteDimensional.of_injective e'.toLinearMap e'.injective

end FiniteDimensionality

section ValuationRingQuotients

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Multiplicative Topology

section ClosedBall

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

private theorem isOpen_setOf_valued_le {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ γ} := by
  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective K v γ
  have hz0 : vK z ≠ 0 := by rw [hz]; exact hγ
  have hr0 : (vK).restrict z ≠ 0 := fun h =>
    hz0 ((Valuation.restrict_eq_zero_iff vK).mp h)
  have hset : {y : v.adicCompletion K | Valued.v y ≤ γ}
      = {y : v.adicCompletion K | (vK).restrict y ≤ (vK).restrict z} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hz]
  rw [hset]
  exact Valued.isOpen_closedBall _ hr0

end ClosedBall

private theorem heightOneSpectrumSubsingletonDVR
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Subsingleton (HeightOneSpectrum O) :=
  ⟨fun a b => IsDedekindDomain.HeightOneSpectrum.ext
    (((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime O).mp
      inferInstance).2.unique ⟨a.3, a.2⟩ ⟨b.3, b.2⟩)⟩

section CompletionQuotient

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

local notation "O_w" => w.toValuationSubring
local notation "𝔪_w" => IsLocalRing.maximalIdeal w.toValuationSubring
local notation "O_W" => w.adicCompletionIntegers
local notation "𝔪_W" => w.heightOneSpectrum.completionIdeal F

theorem algebraMap_mem_completionIdeal_pow_iff (n : ℕ) (x : O_w) :
    algebraMap (O_w) (O_W) x ∈ (𝔪_W) ^ n ↔ x ∈ (𝔪_w) ^ n := by
  have hval : Valued.v (algebraMap (O_w) (O_W) x).val
      = w.heightOneSpectrum.intValuation x := by
    have h1 : (algebraMap (O_w) (O_W) x).val
        = ((algebraMap (O_w) F x : F) : w.adicCompletion) := rfl
    rw [h1, valuedAdicCompletion_eq_valuation' (K := F) w.heightOneSpectrum,
      valuation_of_algebraMap]
  rw [adicCompletion.mem_completionIdeal_pow, hval, ← WithZero.exp_eq_coe_ofAdd,
    intValuation_le_pow_iff_mem, w.heightOneSpectrum_asIdeal]

theorem exists_sub_mem_completionIdeal_pow (n : ℕ) (y : O_W) :
    ∃ x : O_w, y - algebraMap (O_w) (O_W) x ∈ (𝔪_W) ^ n := by
  have hball_open : IsOpen {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} :=
    (isOpen_setOf_valued_le F w.heightOneSpectrum
      WithZero.exp_ne_zero).preimage (continuous_sub_right y.val)
  have hy_mem : y.val ∈ {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} := by
    simp only [Set.mem_ofPred_eq, sub_self, _root_.map_zero]; exact zero_le
  have hmeet := mem_closure_iff.mp
    ((denseRange_algebraMap F w.heightOneSpectrum) y.val) _ hball_open hy_mem
  have hexists : ∃ z : F, Valued.v (algebraMap F w.adicCompletion z - y.val)
      ≤ WithZero.exp (-(n : ℤ)) := by
    rcases hmeet with ⟨z₀, hz₀_ball, z, hz_eq⟩
    exact ⟨z, hz_eq ▸ hz₀_ball⟩
  obtain ⟨z, hz⟩ := hexists
  rw [show algebraMap F w.adicCompletion z = ((z : F) : w.adicCompletion) from rfl] at hz
  have hz_val_le : w.heightOneSpectrum.valuation F z ≤ 1 := by
    have hzhat : Valued.v ((z : w.adicCompletion)) ≤ (1 : ℤᵐ⁰) := by
      calc Valued.v ((z : w.adicCompletion))
          = Valued.v (((z : w.adicCompletion) - y.val) + y.val) := by ring_nf
        _ ≤ max (Valued.v ((z : w.adicCompletion) - y.val)) (Valued.v y.val) :=
            Valuation.map_add _ _ _
        _ ≤ (1 : ℤᵐ⁰) := max_le
            (hz.trans (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)))
            y.2
    rwa [valuedAdicCompletion_eq_valuation'] at hzhat
  have hz_mem : z ∈ (O_w : ValuationSubring F) := by
    obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one F z
      (fun v' => by
        let := heightOneSpectrumSubsingletonDVR (O := O_w)
        obtain rfl : v' = w.heightOneSpectrum := Subsingleton.elim _ _
        exact hz_val_le)
    exact hr ▸ r.2
  refine ⟨⟨z, hz_mem⟩, ?_⟩
  rw [adicCompletion.mem_completionIdeal_pow, ← WithZero.exp_eq_coe_ofAdd]
  have hsub : (y - algebraMap (O_w) (O_W) ⟨z, hz_mem⟩ : O_W).val
      = y.val - ((z : F) : w.adicCompletion) := rfl
  rw [hsub, Valuation.map_sub_swap]
  exact hz

/-- The equivalence of valuation-ring and completed valuation-ring quotients at the specified
depth. -/
def completionQuotientRingEquiv (n : ℕ) :
    (O_w) ⧸ (𝔪_w) ^ n ≃+* (O_W) ⧸ (𝔪_W) ^ n :=
  RingEquiv.ofBijective
    (Ideal.quotientMap _ (algebraMap (O_w) (O_W))
      (fun x hx => (algebraMap_mem_completionIdeal_pow_iff w n x).mpr hx))
    ⟨Ideal.quotientMap_injective'
      (fun x hx => (algebraMap_mem_completionIdeal_pow_iff w n x).mp
        (Ideal.mem_comap.mp hx)),
    fun y => by
      obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨x, hx⟩ := exists_sub_mem_completionIdeal_pow w n y'
      refine ⟨Ideal.Quotient.mk _ x, ?_⟩
      change Ideal.Quotient.mk ((𝔪_W)^n) (algebraMap (O_w) (O_W) x) =
        Ideal.Quotient.mk ((𝔪_W)^n) y'
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (by
        rw [← neg_sub, neg_mem_iff]; exact hx)⟩

theorem completionQuotientRingEquiv_mk (n : ℕ) (x : O_w) :
    completionQuotientRingEquiv w n (Ideal.Quotient.mk _ x)
      = Ideal.Quotient.mk _ (algebraMap (O_w) (O_W) x) := rfl

end CompletionQuotient

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

private theorem valuationSubringScalarTower :
    IsScalarTower K u.toValuationSubring u.adicCompletionIntegers := by
  refine IsScalarTower.of_algebraMap_eq fun k => ?_
  apply Subtype.ext
  change algebraMap K u.adicCompletion k
    = (algebraMap u.toValuationSubring u.adicCompletionIntegers (algebraMap K _ k)).val
  rw [IsScalarTower.algebraMap_apply K L u.adicCompletion]
  rfl

theorem span_irreducible_eq_completionIdeal_pow_one
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) :
    (Ideal.span {πh} : Ideal u.adicCompletionIntegers)
      = (u.heightOneSpectrum.completionIdeal L) ^ 1 := by
  rw [pow_one, ← hπh.maximalIdeal_eq]

/-- The base-field algebra equivalence between valuation-ring and completed valuation-ring
quotients. -/
def completionQuotientAlgEquiv (n : ℕ) :
    (u.toValuationSubring ⧸ (IsLocalRing.maximalIdeal u.toValuationSubring) ^ n)
      ≃ₐ[K] (u.adicCompletionIntegers ⧸ (u.heightOneSpectrum.completionIdeal L) ^ n) :=
  { completionQuotientRingEquiv u n with
    commutes' := fun k => by
      let := valuationSubringScalarTower u
      change completionQuotientRingEquiv u n (algebraMap K _ k) = algebraMap K _ k
      rw [IsScalarTower.algebraMap_apply K u.toValuationSubring
          (u.toValuationSubring ⧸ (IsLocalRing.maximalIdeal u.toValuationSubring) ^ n),
        Ideal.Quotient.algebraMap_eq, completionQuotientRingEquiv_mk,
        IsScalarTower.algebraMap_apply K u.adicCompletionIntegers
          (u.adicCompletionIntegers ⧸ (u.heightOneSpectrum.completionIdeal L) ^ n),
        Ideal.Quotient.algebraMap_eq,
        IsScalarTower.algebraMap_apply K u.toValuationSubring u.adicCompletionIntegers] }

/-- The residue-field identification of the integral completion quotient by an irreducible
element. -/
def quotientByUniformizerEquivResidueField (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) :
    (u.adicCompletionIntegers ⧸ (Ideal.span {πh} : Ideal u.adicCompletionIntegers))
      ≃ₗ[K] u.ResidueField :=
  (Ideal.quotientEquivAlgOfEq K
      (span_irreducible_eq_completionIdeal_pow_one u πh hπh)).toLinearEquiv.trans
    ((completionQuotientAlgEquiv u 1).symm.toLinearEquiv.trans
      (Ideal.quotientEquivAlgOfEq K
        (pow_one (IsLocalRing.maximalIdeal u.toValuationSubring))).toLinearEquiv)

theorem cotangentQuotientFinite : CotangentQuotientFinite K L := by
  intro u _ πh hπh
  have : Module.Finite K u.ResidueField := FiniteResidue.finite
  exact Module.Finite.equiv (quotientByUniformizerEquivResidueField u πh hπh).symm

theorem poleWindowFinite : PoleWindowFinite K L :=
  poleWindowFinite_of_quotientPowersFinite
    (quotientPowersFinite_of_cotangent
      cotangentQuotientFinite)

end ValuationRingQuotients

end AlgebraicCurve.Place.CompletionQuotients
