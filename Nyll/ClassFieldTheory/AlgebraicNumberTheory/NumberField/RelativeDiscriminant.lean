/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.FractionalIdealFactorization
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.IdealNormCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FinitePlaceContraction
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization

/-! # The relative ideal discriminant as the genuine ideal norm of the different -/

@[expose] public section

open scoped NumberField nonZeroDivisors
open ClassFieldTheory
open NumberField IsDedekindDomain UniqueFactorizationMonoid
open ClassFieldTheory.FractionalIdealFactorization

namespace AlgebraicNumberTheory.Discriminant

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in
private theorem ringOfIntegers_moduleFinite : Module.Finite (𝓞 K) (𝓞 L) := by
  let : Module.Finite ℤ (𝓞 L) := inferInstance
  exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)

/-- The different of the number-field integer rings is nonzero. -/
theorem relativeDifferentIdeal_ne_bot : differentIdeal (𝓞 K) (𝓞 L) ≠ ⊥ := by
  let : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have : Module.Finite (𝓞 K) (𝓞 L) := ringOfIntegers_moduleFinite K L
  exact differentIdeal_ne_bot

/-- The actual different of the integer rings, viewed as an invertible fractional ideal. -/
noncomputable def relativeDifferentFractionalIdeal : NumberFieldFractionalIdealGroup L :=
  FractionalIdeal.mk0 L ⟨differentIdeal (𝓞 K) (𝓞 L),
    mem_nonZeroDivisors_iff_ne_zero.mpr (relativeDifferentIdeal_ne_bot K L)⟩

private theorem relativeDifferentNorm_count_nonneg (v : HeightOneSpectrum (𝓞 K)) :
    0 ≤ NumberFieldFractionalIdealGroup.countVector
      (ClassFieldTheory.fractionalIdealNorm K L (relativeDifferentFractionalIdeal K L)) v := by
  classical
  rw [NumberFieldFractionalIdealGroup.countVector_apply, RayClass.count_fractionalIdealNorm,
    ClassFieldTheory.fractionalIdealNormExponentMap_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro W _
  split_ifs
  · exact mul_nonneg (Int.natCast_nonneg _)
      (FractionalIdeal.count_coeIdeal_nonneg L W (differentIdeal (𝓞 K) (𝓞 L)))
  · exact le_rfl

/-- The relative discriminant ideal retains the exponents of the genuine ideal norm of the
actual different. Those exponents are nonnegative. -/
noncomputable def relativeDiscriminantIdeal : Ideal (𝓞 K) :=
  (NumberFieldFractionalIdealGroup.countVector
    (ClassFieldTheory.fractionalIdealNorm K L (relativeDifferentFractionalIdeal K L))).prod
      fun v n => v.asIdeal ^ n.toNat

/-- Coercing the relative discriminant to fractional ideals recovers the norm of the different. -/
theorem relativeDiscriminantIdeal_coe :
    (relativeDiscriminantIdeal K L : FractionalIdeal (𝓞 K)⁰ K) =
      (ClassFieldTheory.fractionalIdealNorm K L (relativeDifferentFractionalIdeal K L) :
        FractionalIdeal (𝓞 K)⁰ K) := by
  let D := ClassFieldTheory.fractionalIdealNorm K L (relativeDifferentFractionalIdeal K L)
  let e := NumberFieldFractionalIdealGroup.countVector D
  have hfactor : NumberFieldFractionalIdealGroup.factorization (Multiplicative.ofAdd e) = D :=
    (NumberFieldFractionalIdealGroup.factorizationEquiv (K := K)).apply_symm_apply D
  change (FractionalIdeal.coeIdealHom (𝓞 K)⁰ K)
    (e.prod fun v n => v.asIdeal ^ n.toNat) = (D : FractionalIdeal (𝓞 K)⁰ K)
  rw [← hfactor, NumberFieldFractionalIdealGroup.factorization_val, toAdd_ofAdd,
    map_finsuppProd]
  apply Finsupp.prod_congr
  intro v _
  change ((v.asIdeal ^ (e v).toNat : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
    (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ e v
  rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast,
    Int.toNat_of_nonneg (relativeDifferentNorm_count_nonneg K L v)]

theorem relativeDiscriminantIdeal_ne_bot : relativeDiscriminantIdeal K L ≠ ⊥ := by
  apply (FractionalIdeal.coeIdeal_ne_zero (K := K)).mp
  rw [relativeDiscriminantIdeal_coe]
  exact Units.ne_zero _

open scoped Classical in
/-- The exponent in the relative discriminant is the residue-degree-weighted sum of the
different exponents over the selected base place. -/
theorem count_relativeDiscriminantIdeal (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (relativeDiscriminantIdeal K L : FractionalIdeal (𝓞 K)⁰ K) =
      (NumberFieldFractionalIdealGroup.countVector (relativeDifferentFractionalIdeal K L)).sum
        fun W n => if _root_.finitePlaceBelow (K := K) W = v then
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * n else 0 := by
  classical
  rw [relativeDiscriminantIdeal_coe, RayClass.count_fractionalIdealNorm,
    ClassFieldTheory.fractionalIdealNormExponentMap_apply]

private theorem different_count_ne_zero_iff_ramified (W : HeightOneSpectrum (𝓞 L)) :
    NumberFieldFractionalIdealGroup.countVector (relativeDifferentFractionalIdeal K L) W ≠ 0 ↔
      ¬ Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
  classical
  let : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  have : Module.Finite (𝓞 K) (𝓞 L) := ringOfIntegers_moduleFinite K L
  let D := differentIdeal (𝓞 K) (𝓞 L)
  have hD : D ≠ ⊥ := relativeDifferentIdeal_ne_bot K L
  change FractionalIdeal.count L W (D : FractionalIdeal (𝓞 L)⁰ L) ≠ 0 ↔ _
  rw [count_coeIdeal_eq_multiplicity (F := L) W hD, Nat.cast_ne_zero,
    multiplicity_ne_zero_iff_le W hD, ← Ideal.dvd_iff_le]
  exact dvd_differentIdeal_iff (A := 𝓞 K) (B := 𝓞 L) (P := W.asIdeal)

/-- A prime has nonzero discriminant exponent exactly when an upstairs prime over it ramifies. -/
theorem count_relativeDiscriminantIdeal_ne_zero_iff_ramified (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v (relativeDiscriminantIdeal K L : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 ↔
      ∃ W : HeightOneSpectrum (𝓞 L),
        W.asIdeal.LiesOver v.asIdeal ∧ ¬ Algebra.IsUnramifiedAt (𝓞 K) W.asIdeal := by
  classical
  let e := NumberFieldFractionalIdealGroup.countVector (relativeDifferentFractionalIdeal K L)
  let degreeTerm (W : HeightOneSpectrum (𝓞 L)) : ℤ :=
    if _root_.finitePlaceBelow (K := K) W = v then (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W else 0
  rw [count_relativeDiscriminantIdeal K L v, Finsupp.sum]
  change (∑ W ∈ e.support, degreeTerm W) ≠ 0 ↔ _
  constructor
  · intro h
    by_contra hn
    apply h
    apply Finset.sum_eq_zero
    intro W hW
    by_cases hWv : _root_.finitePlaceBelow (K := K) W = v
    · exact (hn ⟨W, ⟨(congrArg HeightOneSpectrum.asIdeal hWv).symm⟩,
        (different_count_ne_zero_iff_ramified K L W).mp (Finsupp.mem_support_iff.mp hW)⟩).elim
    · change (if _root_.finitePlaceBelow (K := K) W = v then
          (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W else 0) = 0
      rw [ite_eq_right hWv]
  · rintro ⟨W, hWv, hW⟩
    let : W.asIdeal.LiesOver v.asIdeal := hWv
    have : Module.Finite (𝓞 K) (𝓞 L) := ringOfIntegers_moduleFinite K L
    have hWabove : _root_.finitePlaceBelow (K := K) W = v := by
      apply HeightOneSpectrum.ext
      exact (Ideal.over_def W.asIdeal v.asIdeal).symm
    have hcount (P : HeightOneSpectrum (𝓞 L)) : 0 ≤ e P :=
      FractionalIdeal.count_coeIdeal_nonneg L P (differentIdeal (𝓞 K) (𝓞 L))
    have hterm (P : HeightOneSpectrum (𝓞 L)) : 0 ≤ degreeTerm P := by
      change 0 ≤ if _root_.finitePlaceBelow (K := K) P = v then
        (P.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e P else 0
      split_ifs
      · exact mul_nonneg (Int.natCast_nonneg _) (hcount P)
      · exact le_rfl
    have he : e W ≠ 0 := (different_count_ne_zero_iff_ramified K L W).mpr hW
    have hpos : 0 < degreeTerm W := by
      change 0 < if _root_.finitePlaceBelow (K := K) W = v then
        (W.asIdeal.inertiaDeg (𝓞 K) : ℤ) * e W else 0
      rw [ite_eq_left hWabove]
      exact mul_pos (Int.natCast_pos.mpr (Ideal.inertiaDeg_pos W.asIdeal (𝓞 K)))
        (lt_of_le_of_ne (hcount W) he.symm)
    exact (hpos.trans_le (Finset.single_le_sum (fun P _ => hterm P)
      (Finsupp.mem_support_iff.mpr he))).ne'

end AlgebraicNumberTheory.Discriminant
