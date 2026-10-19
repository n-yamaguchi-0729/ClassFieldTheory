/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_exists_polynomial_isUnit_aeval_imp_etale_levelSet.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.TensorProduct.Maps
import Nyll.SchemeTheory.RingTheory.LinearAlgebra.AlgebraLevelSetFiniteFreeFinrank
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Choose

/-!
# Algebra exists polynomial is Unit aeval imp etale level Set
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Polynomial.Proofs
namespace Algebra_exists_polynomial_isUnit_aeval_imp_etale_levelSet

universe u

open scoped TensorProduct
open _root_.Polynomial

namespace NoncritCore

open Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b (levelSetEquiv)

section Sep

theorem isSeparable_of_natCast_finrank_ne_zero (F E : Type u) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (h : (Module.finrank F E : F) ≠ 0) : Algebra.IsSeparable F E := by
  let S := separableClosure F E
  let _ : IsPurelyInseparable S E := separableClosure.isPurelyInseparable F E
  obtain ⟨q, hq⟩ := ExpChar.exists F
  let _ := hq
  let _ : ExpChar S q := expChar_of_injective_ringHom (algebraMap F S).injective q
  obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow S E q
  have htower : Module.finrank F S * Module.finrank S E = Module.finrank F E :=
    Module.finrank_mul_finrank F S E
  have h1 : Module.finrank S E = 1 := by
    rcases hq with _ | ⟨hprime⟩
    · simpa using hn
    · cases n with
      | zero => simpa using hn
      | succ n =>
        exfalso
        apply h
        have hdvd : q ∣ Module.finrank F E := by
          rw [← htower, hn, pow_succ]
          exact dvd_mul_of_dvd_right (dvd_mul_left q _) _
        obtain ⟨c, hc⟩ := hdvd
        rw [hc, Nat.cast_mul, CharP.cast_eq_zero F q, zero_mul]
  have htop : S = ⊤ := by
    have hbot : (⊥ : Subalgebra S E) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (⊤ : Subalgebra S E) := Algebra.mem_top
    rw [← hbot, Algebra.mem_bot] at hx
    obtain ⟨y, rfl⟩ := hx
    exact y.2
  exact (separableClosure.eq_top_iff F E).mp htop

end Sep

section Core

/-- The polynomial-ring algebra structure that sends the variable to the chosen element. -/
noncomputable abbrev algOfElt (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (s : S) :
    Algebra R[X] S := (Polynomial.aeval s : R[X] →ₐ[R] S).toRingHom.toAlgebra

theorem isScalarTower_algOfElt (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (s : S) :
    letI := algOfElt R S s; IsScalarTower R R[X] S :=
  letI := algOfElt R S s
  IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R S r = (Polynomial.aeval s : R[X] →ₐ[R] S) (algebraMap R R[X] r)
    rw [AlgHom.commutes]

theorem algebraMap_algOfElt_X (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (s : S) :
    letI := algOfElt R S s; algebraMap R[X] S X = s := by
  change (Polynomial.aeval s : R[X] →ₐ[R] S) X = s
  exact Polynomial.aeval_X s

section Omega
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The base-change equivalence for the module of Kähler differentials. -/
noncomputable def omegaEquiv (P : Type u) [CommRing P] (A : Type u) [CommRing A] [Algebra P A]
    (S : Type u) [CommRing S] [Algebra P S] :
    S ⊗[P] Ω[A⁄P] ≃ₗ[S] Ω[(S ⊗[P] A)⁄S] :=
  (KaehlerDifferential.isBaseChange P S A (S ⊗[P] A)).equiv

end Omega

theorem subsingleton_tensor_of_smul_eq_zero {P : Type u} [CommRing P] {T : Type u} [Field T]
  [Algebra P T]
    {N : Type u} [AddCommGroup N] [Module P N] (q : P) (hq : algebraMap P T q ≠ 0)
    (hN : ∀ y : N, q • y = 0) : Subsingleton (T ⊗[P] N) := by
  refine ⟨fun z w => ?_⟩
  suffices h : ∀ z : T ⊗[P] N, z = 0 by rw [h z, h w]
  intro z
  have key : algebraMap P T q • z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul c y =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, ← Algebra.smul_def, TensorProduct.smul_tmul, hN,
        TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  have := congrArg (fun w => (algebraMap P T q)⁻¹ • w) key
  simp only [smul_zero, ← mul_smul, inv_mul_cancel₀ hq, one_smul] at this
  exact this

theorem subsingleton_tensor_kaehler_of_isDomain (P : Type u) [CommRing P] (A : Type u) [CommRing A]
    [Algebra P A] (K : Type u) [Field K] [Algebra P K]
    [IsDomain (K ⊗[P] A)] [Module.Finite K (K ⊗[P] A)]
    (h : (Module.finrank K (K ⊗[P] A) : K) ≠ 0) : Subsingleton (K ⊗[P] Ω[A⁄P]) := by
  let T : Type u := K ⊗[P] A
  let _ : Algebra.IsIntegral K T := Algebra.IsIntegral.of_finite K T
  have hT : IsField T := isField_of_isIntegral_of_isField' (Field.toIsField K)
  let _ : Field T := hT.toField
  let _ : Algebra.IsSeparable K T := isSeparable_of_natCast_finrank_ne_zero K T h
  let _ : Algebra.FormallyUnramified K T := Algebra.FormallyUnramified.of_isSeparable K T
  exact (omegaEquiv P A K).toEquiv.subsingleton

theorem exists_ne_zero_smul_baseChange_eq_zero (P : Type u) [CommRing P] (A : Type u) [CommRing A]
    [Algebra P A] (M : Type u) [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower P A M]
    [Module.Finite A M]
    (Pk : Type u) [CommRing Pk] [IsDomain Pk] [Algebra P Pk] (K : Type u) [Field K] [Algebra Pk K]
    [IsFractionRing Pk K] [Algebra P K] [IsScalarTower P Pk K] [Subsingleton (K ⊗[P] M)] :
    ∃ D : Pk, D ≠ 0 ∧ ∀ y : Pk ⊗[P] M, D • y = 0 := by
  classical
  let Mk : Type u := Pk ⊗[P] M
  let _ : Subsingleton (K ⊗[Pk] Mk) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange P Pk K K M).toEquiv.subsingleton
  have hlocM : IsLocalizedModule (nonZeroDivisors Pk) (TensorProduct.mk Pk K Mk 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors Pk) K _).mpr
      (TensorProduct.isBaseChange Pk Mk K)
  have htors : ∀ y : Mk, ∃ q : nonZeroDivisors Pk, (q : Pk) • y = 0 := fun y => by
    obtain ⟨q, hq⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors Pk)
      (TensorProduct.mk Pk K Mk 1) (m := y)).mp (Subsingleton.elim _ _)
    exact ⟨q, hq⟩
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := A) (M := M)
  choose q hq using fun g : M => htors ((1 : Pk) ⊗ₜ[P] g)
  let D₀ : Pk := ∏ g ∈ G, (q g : Pk)
  have hD₀mem : D₀ ∈ nonZeroDivisors Pk := prod_mem fun g _ => (q g).2
  refine ⟨D₀, nonZeroDivisors.ne_zero hD₀mem, ?_⟩
  have hkillG : ∀ g ∈ G, D₀ • ((1 : Pk) ⊗ₜ[P] g : Mk) = 0 := by
    intro g hg
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun g => (q g : Pk)) hg
    change (∏ i ∈ G, (q i : Pk)) • _ = 0
    rw [hr, mul_comm, mul_smul, hq, smul_zero]
  intro y
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  | tmul c x =>
    have hx : x ∈ Submodule.span A (G : Set M) := by rw [hG]; exact Submodule.mem_top
    induction hx using Submodule.span_induction generalizing c with
    | mem g hg =>
      have : (c ⊗ₜ[P] g : Mk) = c • ((1 : Pk) ⊗ₜ[P] g) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, smul_comm, hkillG g hg, smul_zero]
    | zero => rw [TensorProduct.tmul_zero, smul_zero]
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, smul_add, hx, hy, add_zero]
    | smul a x _ hx =>
      let φ : M →ₗ[P] M := (DistribSMul.toLinearMap A M a).restrictScalars P
      have : (c ⊗ₜ[P] (a • x) : Mk) = (φ.baseChange Pk) (c ⊗ₜ[P] x) := by
        rw [LinearMap.baseChange_tmul]
        rfl
      rw [this, ← LinearMap.map_smul_of_tower, hx c, map_zero]

theorem etale_baseChange_of_subsingleton (P : Type u) [CommRing P] (A : Type u) [CommRing A]
    [Algebra P A] [Algebra.FinitePresentation P A]
    (S : Type u) [CommRing S] [IsLocalRing S] [Algebra P S]
    [Module.Finite S (S ⊗[P] A)] [Module.Free S (S ⊗[P] A)]
    (h : Subsingleton (IsLocalRing.ResidueField S ⊗[S] (S ⊗[P] Ω[A⁄P]))) :
    Algebra.Etale S (S ⊗[P] A) := by
  let TS : Type u := S ⊗[P] A
  let _ : Algebra.FinitePresentation S TS := Algebra.FinitePresentation.baseChange S
  let _ : Module.Finite TS Ω[TS⁄S] := KaehlerDifferential.finite S TS
  let _ : Module.Finite S Ω[TS⁄S] := Module.Finite.trans TS Ω[TS⁄S]
  let _ : Subsingleton (IsLocalRing.ResidueField S ⊗[S] Ω[TS⁄S]) :=
    (TensorProduct.congr (LinearEquiv.refl S (IsLocalRing.ResidueField S))
      ((omegaEquiv P A S).restrictScalars S)).symm.toEquiv.subsingleton
  let _ : Subsingleton Ω[TS⁄S] := (IsLocalRing.subsingleton_tensorProduct (R := S)).mp inferInstance
  let _ : Algebra.FormallyUnramified S TS := (Algebra.formallyUnramified_iff S TS).mpr inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat


theorem core (R : Type u) [CommRing R] [IsLocalRing R]
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    [IsDomain (IsLocalRing.ResidueField R ⊗[R] A)]
    (f : A) (m : ℕ) (hm : IsUnit (m : R))
    (hls : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
        Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) = m) :
    ∃ D : Polynomial R, (∃ i, IsUnit (D.coeff i)) ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (s :
        S),
        IsUnit (Polynomial.aeval s D) →
        Algebra.Etale S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) := by
  classical
  let _ : Algebra R[X] A := algOfElt R A f
  let _ : IsScalarTower R R[X] A := isScalarTower_algOfElt R A f
  have hfX : algebraMap R[X] A X = f := algebraMap_algOfElt_X R A f
  let _ : Algebra.FiniteType R[X] A := Algebra.FiniteType.of_restrictScalars_finiteType R R[X] A
  let _ : Algebra.FinitePresentation R[X] A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R R[X] A
  set k : Type u := IsLocalRing.ResidueField R with hk
  set M : Type u := Ω[A⁄R[X]] with hM
  let _ : Module.Finite A M := KaehlerDifferential.finite R[X] A
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm.ne_zero (Nat.cast_zero)
  have hmk : ((m : ℕ) : k) ≠ 0 := (hm.map (algebraMap R k)).ne_zero
  let _ : Algebra R[X] k[X] := (Polynomial.mapRingHom (algebraMap R k)).toAlgebra
  let _ : IsScalarTower R R[X] k[X] := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R k[X] r = Polynomial.map (algebraMap R k) (algebraMap R R[X] r)
    rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, Polynomial.map_C]
    rfl
  have hPkX : algebraMap R[X] k[X] X = X := Polynomial.map_X _
  let K : Type u := RatFunc k
  let _ : IsScalarTower R R[X] K := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R k[X] K, IsScalarTower.algebraMap_apply R R[X] k[X],
      ← IsScalarTower.algebraMap_apply R[X] k[X] K]
  have hKX : algebraMap R[X] K X = algebraMap k[X] K X := by
    rw [IsScalarTower.algebraMap_apply R[X] k[X] K, hPkX]
  let T : Type u := K ⊗[R[X]] A
  obtain ⟨hfinK, hfreeK, hrankK⟩ := hls K (algebraMap k[X] K X)
  let e₁ : (K ⊗[R] A ⧸ Ideal.span {(1 : K) ⊗ₜ[R] f - (algebraMap k[X] K X) ⊗ₜ[R] (1 : A)}) ≃ₐ[K] T
    :=
    levelSetEquiv R A K f (algebraMap k[X] K X) hfX hKX
  let _ : Module.Finite K T := Module.Finite.equiv e₁.toLinearEquiv
  let _ : Module.Free K T := Module.Free.of_equiv e₁.toLinearEquiv
  have hrankT : Module.finrank K T = m := by rw [← e₁.toLinearEquiv.finrank_eq, hrankK]
  let _ : Nontrivial T := Module.nontrivial_of_finrank_pos (R := K) (by rw [hrankT]; omega)
  let J : Ideal A := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  let Abar : Type u := A ⧸ J
  let _ : IsDomain Abar :=
    MulEquiv.isDomain (k ⊗[R] A)
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (IsLocalRing.maximalIdeal
        R)).toMulEquiv.trans
        (Algebra.TensorProduct.comm R A k).toMulEquiv)
  have hJ : J ≠ ⊤ := fun h => not_subsingleton Abar (Ideal.Quotient.subsingleton_iff.mpr h)
  let _ : J.LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ hJ) Ideal.le_comap_map)⟩
  let _ : Algebra k Abar := Ideal.Quotient.algebraOfLiesOver J (IsLocalRing.maximalIdeal R)
  let _ : IsScalarTower R k Abar := IsScalarTower.of_algebraMap_eq fun r => rfl
  have hkAbar : ∀ r : R, algebraMap k Abar (algebraMap R k r) = Ideal.Quotient.mk J (algebraMap R A
    r) :=
    fun r => rfl
  let eA : k ⊗[R] A ≃+* Abar :=
    (Algebra.TensorProduct.comm R k A).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (IsLocalRing.maximalIdeal
        R)).symm.toRingEquiv
  have heA : ∀ (c : k) (a : A), eA (c ⊗ₜ[R] a) = algebraMap k Abar c * Ideal.Quotient.mk J a := by
    intro c a
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
    change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (IsLocalRing.maximalIdeal R)).symm
        (a ⊗ₜ[R] (Ideal.Quotient.mk _ r)) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
    change Ideal.Quotient.mk J (r • a) = algebraMap k Abar (algebraMap R k r) * Ideal.Quotient.mk J
      a
    rw [hkAbar, ← map_mul, Algebra.smul_def]
  let eAk : k ⊗[R] A ≃ₐ[k] Abar :=
    AlgEquiv.ofRingEquiv (f := eA) fun c => by
      change eA (c ⊗ₜ[R] (1 : A)) = algebraMap k Abar c
      rw [heA, map_one, mul_one]
  have heAk : ∀ a : A, eAk ((1 : k) ⊗ₜ[R] a) = Ideal.Quotient.mk J a := fun a => by
    change eA ((1 : k) ⊗ₜ[R] a) = _
    rw [heA, map_one, one_mul]
  let _ : Algebra k[X] Abar := algOfElt k Abar (Ideal.Quotient.mk J f)
  let _ : IsScalarTower k k[X] Abar := isScalarTower_algOfElt k Abar _
  have hAbarX : algebraMap k[X] Abar X = Ideal.Quotient.mk J f := algebraMap_algOfElt_X k Abar _
  let c₀ : (K ⊗[R] A) ≃ₐ[K] K ⊗[k] Abar :=
    (Algebra.TensorProduct.cancelBaseChange R k K K A).symm.trans
      (Algebra.TensorProduct.congr AlgEquiv.refl eAk)
  have hc₀ : ∀ (x : K) (a : A), c₀ (x ⊗ₜ[R] a) = x ⊗ₜ[k] Ideal.Quotient.mk J a := by
    intro x a
    have h1 : (Algebra.TensorProduct.cancelBaseChange R k K K A).symm (x ⊗ₜ[R] a)
        = x ⊗ₜ[k] ((1 : k) ⊗ₜ[R] a) := by
      apply (Algebra.TensorProduct.cancelBaseChange R k K K A).injective
      rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    change Algebra.TensorProduct.congr AlgEquiv.refl eAk
        ((Algebra.TensorProduct.cancelBaseChange R k K K A).symm (x ⊗ₜ[R] a)) = _
    rw [h1, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    change x ⊗ₜ[k] eAk ((1 : k) ⊗ₜ[R] a) = _
    rw [heAk]
  have hrel : Ideal.span
      {(1 : K) ⊗ₜ[k] Ideal.Quotient.mk J f - (algebraMap k[X] K X) ⊗ₜ[k] (1 : Abar)} =
      (Ideal.span {(1 : K) ⊗ₜ[R] f - (algebraMap k[X] K X) ⊗ₜ[R] (1 : A)}).map c₀ := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, hc₀, hc₀, map_one]
  let e₂ : T ≃ₐ[K] K ⊗[k[X]] Abar :=
    (e₁.symm.trans (Ideal.quotientEquivAlg _ _ c₀ hrel)).trans
      (levelSetEquiv k Abar K (Ideal.Quotient.mk J f) (algebraMap k[X] K X) hAbarX rfl)
  let e₃ : T ≃+* Abar ⊗[k[X]] K :=
    e₂.toRingEquiv.trans (Algebra.TensorProduct.comm k[X] K Abar).toRingEquiv
  let _ : IsLocalization (Algebra.algebraMapSubmonoid Abar (nonZeroDivisors k[X])) (Abar ⊗[k[X]] K)
    :=
    IsLocalization.tensor K (nonZeroDivisors k[X])
  let _ : Nontrivial (Abar ⊗[k[X]] K) := e₃.symm.toEquiv.nontrivial
  have h0 : (0 : Abar) ∉ Algebra.algebraMapSubmonoid Abar (nonZeroDivisors k[X]) := by
    intro h0
    let _ := IsLocalization.uniqueOfZeroMem (S := Abar ⊗[k[X]] K) h0
    exact not_subsingleton (Abar ⊗[k[X]] K) inferInstance
  let _ : IsDomain (Abar ⊗[k[X]] K) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _ (le_nonZeroDivisors_of_noZeroDivisors h0)
  let _ : IsDomain T := MulEquiv.isDomain (Abar ⊗[k[X]] K) e₃.toMulEquiv
  have hmK : ((Module.finrank K T : ℕ) : K) ≠ 0 := by
    rw [hrankT, ← map_natCast (algebraMap k K), _root_.map_ne_zero]
    exact hmk
  let _ : Subsingleton (K ⊗[R[X]] M) := subsingleton_tensor_kaehler_of_isDomain R[X] A K hmK
  let Mk : Type u := k[X] ⊗[R[X]] M
  obtain ⟨D₀, hD₀, hkill⟩ := exists_ne_zero_smul_baseChange_eq_zero R[X] A M k[X] K
  let D₁ : k[X] := D₀ * Polynomial.C (D₀.leadingCoeff)⁻¹
  have hD₁ : D₁.Monic := Polynomial.monic_mul_leadingCoeff_inv hD₀
  have hkill₁ : ∀ y : Mk, D₁ • y = 0 := fun y => by
    change (D₀ * _) • y = 0
    rw [mul_comm, mul_smul, hkill, smul_zero]
  obtain ⟨D, hDmap, -, hDmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts D₁).mpr (Polynomial.map_surjective _ IsLocalRing.residue_surjective D₁))
      hD₁
  refine ⟨D, ⟨D.natDegree, by rw [hDmonic.coeff_natDegree]; exact isUnit_one⟩, ?_⟩
  intro S _ _ _ _ s hs
  let _ : Algebra R[X] S := algOfElt R S s
  let _ : IsScalarTower R R[X] S := isScalarTower_algOfElt R S s
  have hsX : algebraMap R[X] S X = s := algebraMap_algOfElt_X R S s
  let TS : Type u := S ⊗[R[X]] A
  obtain ⟨hfinS, hfreeS, -⟩ := hls S s
  let e : (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ≃ₐ[S] TS :=
    levelSetEquiv R A S f s hfX hsX
  let _ : Module.Finite S TS := Module.Finite.equiv e.toLinearEquiv
  let _ : Module.Free S TS := Module.Free.of_equiv e.toLinearEquiv
  let κ : Type u := IsLocalRing.ResidueField S
  let _ : Algebra R[X] κ := ((IsLocalRing.residue S).comp (algebraMap R[X] S)).toAlgebra
  have hκS : IsScalarTower R[X] S κ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ι : k →+* κ := IsLocalRing.ResidueField.map (algebraMap R S)
  let _ : Algebra k[X] κ := (Polynomial.eval₂RingHom ι (IsLocalRing.residue S s)).toAlgebra
  have htow : ∀ p : R[X], algebraMap k[X] κ (algebraMap R[X] k[X] p) = algebraMap R[X] κ p := by
    intro p
    change Polynomial.eval₂ ι (IsLocalRing.residue S s) (Polynomial.map (algebraMap R k) p)
      = IsLocalRing.residue S ((Polynomial.aeval s : R[X] →ₐ[R] S) p)
    rw [Polynomial.eval₂_map, Polynomial.aeval_def, Polynomial.hom_eval₂]
    rfl
  have hκk : IsScalarTower R[X] k[X] κ :=
    IsScalarTower.of_algebraMap_eq fun p => (htow p).symm
  have hκself : IsScalarTower R[X] κ κ :=
    IsScalarTower.of_algebraMap_eq fun p => by rw [Algebra.algebraMap_self, RingHom.id_apply]
  have hDκ : algebraMap k[X] κ D₁ ≠ 0 := by
    rw [← hDmap]
    change algebraMap k[X] κ (algebraMap R[X] k[X] D) ≠ 0
    rw [htow]
    change IsLocalRing.residue S ((Polynomial.aeval s : R[X] →ₐ[R] S) D) ≠ 0
    exact (hs.map _).ne_zero
  let _ : Subsingleton (κ ⊗[k[X]] Mk) := subsingleton_tensor_of_smul_eq_zero D₁ hDκ hkill₁
  let _ : Subsingleton (κ ⊗[R[X]] M) :=
    (@TensorProduct.AlgebraTensorModule.cancelBaseChange R[X] k[X] κ κ M
      _ _ _ _ _ _ _ _ _ hκk hκself _ _ _ _ _).symm.toEquiv.subsingleton
  have hκ : Subsingleton (κ ⊗[S] (S ⊗[R[X]] M)) :=
    (@TensorProduct.AlgebraTensorModule.cancelBaseChange R[X] S κ κ M
      _ _ _ _ _ _ _ _ _ hκS hκself _ _ _ _ _).toEquiv.subsingleton
  let _ : Algebra.Etale S TS := etale_baseChange_of_subsingleton R[X] A S hκ
  exact Algebra.Etale.of_equiv e.symm

end Core

end NoncritCore

theorem _root_.Algebra.exists_polynomial_isUnit_aeval_imp_etale_levelSet
    (R : Type u) [CommRing R] [IsLocalRing R]
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    [IsDomain (IsLocalRing.ResidueField R ⊗[R] A)]
    (f : A) (m : ℕ) (hm : IsUnit (m : R))
    (hls : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
        Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) = m) :
    ∃ D : Polynomial R, (∃ i, IsUnit (D.coeff i)) ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (s :
        S),
        IsUnit (Polynomial.aeval s D) →
        Algebra.Etale S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) :=
  NoncritCore.core R A f m hm hls
end Algebra_exists_polynomial_isUnit_aeval_imp_etale_levelSet
end AlgebraicCurves.Foundations.Polynomial.Proofs
end ProofImplementation
