/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Finite.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.AbsoluteConstantFrobenius
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.ConstantResidueDegree
import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits

/-!
# Arithmetic constant action of fixed-field Frobenius

The Frobenius chosen by the constant degree datum at any finite fixed field
acts on actual constants by the cardinality of that field's full constants.
The residue-degree index is converted to the actual constant-field degree.
This comparison takes place in one ambient closure, including at intermediate
base fields used in the local-global argument.
-/

noncomputable section

namespace FunctionField

open ClassFormation LocalClassFieldTheory KummerTheory CyclicCohomology

variable (k K Ω : Type) [Field k] [Finite k] [Field K] [Field Ω]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    [IsGalois K Ω] [IsSepClosed Ω]


/-- A natural normalized degree at a finite fixed field is characterized
by the actual arithmetic action on every algebraic constant. -/
theorem fixedFieldNormalizedDegree_eq_nat_iff
    (H : FiniteAbstractField Gal(Ω/K)) (σ : H.field.toSubgroup) (n : ℕ) :
    (fullConstantDegreeData k K Ω).normalizedDegree
        (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω)) σ =
          Multiplicative.ofAdd (n : ZHat) ↔
      ∀ c : separableClosure (algebraicClosure k K) Ω,
        σ.val (c : Ω) =
          (c : Ω) ^ (Nat.card (algebraicClosure k (abstractFixedField K Ω H.field)) ^ n) := by
  let F := abstractFixedField K Ω H.field
  let C := algebraicClosure k K
  have hFfinite : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional K Ω H.field H.finite
  have hKft : Algebra.EssFiniteType k K := essFiniteType k K
  have hKFft : Algebra.EssFiniteType K F := Algebra.EssFiniteType.of_finiteType K F
  have hFft : Algebra.EssFiniteType k F := Algebra.EssFiniteType.comp k K F
  have hCfinite : Finite C := FieldTheory.finite_algebraicClosure_of_finite_base k K
  have hCFfinite : Finite (algebraicClosure k F) :=
    FieldTheory.finite_algebraicClosure_of_finite_base k F
  let D := fullConstantDegreeData k K Ω
  let HR := H.toFiniteResidueAbstractField D
  have hcard : Nat.card (algebraicClosure k F) =
      Nat.card C ^ (HR.residueDegree : ℕ) := by
    rw [Module.natCard_eq_pow_finrank (K := k) (V := algebraicClosure k F),
      Module.natCard_eq_pow_finrank (K := k) (V := C)]
    rw [fullConstants_finrank_eq_mul_residueDegree k K Ω H, pow_mul]
    rfl
  have hdegree : D.normalizedDegree HR σ = Multiplicative.ofAdd (n : ZHat) ↔
      D.degree σ.val = Multiplicative.ofAdd (((HR.residueDegree : ℕ) * n : ℕ) : ZHat) := by
    constructor
    · intro h
      apply Multiplicative.ext
      rw [← D.residueDegree_nsmul_normalizedDegree HR σ, h]
      change (HR.residueDegree : ℕ) • (n : ZHat) =
        (((HR.residueDegree : ℕ) * n : ℕ) : ZHat)
      rw [nsmul_eq_mul, Nat.cast_mul]
    · intro h
      apply Multiplicative.ext
      apply zHatMulNat_injective HR.residueDegree.property
      change (HR.residueDegree : ℕ) • (D.normalizedDegree HR σ).toAdd =
        (HR.residueDegree : ℕ) • (n : ZHat)
      rw [D.residueDegree_nsmul_normalizedDegree HR σ, h]
      change (((HR.residueDegree : ℕ) * n : ℕ) : ZHat) =
        (HR.residueDegree : ℕ) • (n : ZHat)
      rw [nsmul_eq_mul, Nat.cast_mul]
  change D.normalizedDegree HR σ = Multiplicative.ofAdd (n : ZHat) ↔ _
  rw [hdegree]
  change absoluteConstantDegree C K Ω σ.val =
    Multiplicative.ofAdd (((HR.residueDegree : ℕ) * n : ℕ) : ZHat) ↔
      ∀ c : separableClosure C Ω,
        σ.val (c : Ω) = (c : Ω) ^ (Nat.card (algebraicClosure k F) ^ n)
  rw [hcard]
  simpa only [pow_mul] using
    absoluteConstantDegree_eq_nat_iff C K Ω σ.val ((HR.residueDegree : ℕ) * n)

/-- The actual fixed-field automorphism defined by normalized degree one
raises constants to the cardinality of the full constants of its base. -/
theorem fixedFieldFrobenius_constant_action
    (H : FiniteAbstractField Gal(Ω/K)) (T : FiniteGaloisSubextension H.field) :
    let _ : Algebra (abstractFixedField K Ω H.field) (abstractFixedField K Ω T.field) :=
      (IntermediateField.inclusion (abstractFixedField_le K Ω T.below)).toRingHom.toAlgebra
    ∀ x : abstractFixedField K Ω T.field,
      IsSeparable (algebraicClosure k K) (x : Ω) →
      ((abstractExtensionQuotientEquivGaloisGroup K Ω H.field T.field T.below T.normal
        (T.extensionQuotientMulEquiv.symm
          ((fullConstantDegreeData k K Ω).unramifiedFrobenius
            (H.toFiniteResidueAbstractField (fullConstantDegreeData k K Ω))
            T.field T.below)) x : abstractFixedField K Ω T.field) : Ω) =
        (x : Ω) ^ Nat.card (algebraicClosure k (abstractFixedField K Ω H.field)) := by
  intro aFE x hx
  let F := abstractFixedField K Ω H.field
  let C := algebraicClosure k K
  let D := fullConstantDegreeData k K Ω
  let HR := H.toFiniteResidueAbstractField D
  let σ : H.field.toSubgroup := Classical.choose
    (D.normalizedDegree_surjective HR (Multiplicative.ofAdd (1 : ZHat)))
  have hσ : D.normalizedDegree HR σ = Multiplicative.ofAdd (1 : ZHat) :=
    Classical.choose_spec
      (D.normalizedDegree_surjective HR (Multiplicative.ofAdd (1 : ZHat)))
  have hpow := (fixedFieldNormalizedDegree_eq_nat_iff k K Ω H σ 1).mp
    (by simpa only [Nat.cast_one] using hσ)
  let eG : T.extensionQuotient ≃*
      Gal((abstractFixedField K Ω T.field)/(abstractFixedField K Ω H.field)) :=
    abstractExtensionQuotientEquivGaloisGroup K Ω H.field T.field T.below T.normal
  have hv : σ.val (x : Ω) =
      ((eG (QuotientGroup.mk' (extensionSubgroup H.field T.field T.below) σ)) x : Ω) :=
    abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
      K Ω H.field T.field T.below T.normal σ x
  have hq : T.extensionQuotientMulEquiv.symm
      (D.unramifiedFrobenius HR T.field T.below) =
      QuotientGroup.mk' (extensionSubgroup H.field T.field T.below) σ := rfl
  change (((eG (T.extensionQuotientMulEquiv.symm
    (D.unramifiedFrobenius HR T.field T.below))) x :
      abstractFixedField K Ω T.field) : Ω) = (x : Ω) ^ Nat.card (algebraicClosure k F)
  rw [hq]
  simpa only [pow_one] using
    hv.symm.trans (hpow ⟨(x : Ω), mem_separableClosure_iff.mpr hx⟩)

end FunctionField
