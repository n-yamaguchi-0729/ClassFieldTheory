/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompleteValuations
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusLift
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismTransport

/-!
# Frobenius on the actual completed valuation rings

Coefficient Frobenius preserves the native Laurent valuation. Its completed
lift consequently preserves the selected integral closure, by transporting
integral equations along the coefficient-ring automorphism. The resulting
integer-ring equivalence retains the actual completed field action.
-/

@[expose] public section

noncomputable section

open scoped LaurentSeries PowerSeries

universe u v w

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

variable {K : Type u} [Field K]

/-- Coefficient Frobenius on the original Laurent valuation ring. -/
noncomputable def equalCharacteristicCompletedUnramifiedFrobeniusIntegerEquiv
    (k : Type w) [Field k] [Finite k] :
    (equalCharacteristicCompletedUnramifiedCompleteDVF k).valuationSubring ≃+*
      (equalCharacteristicCompletedUnramifiedCompleteDVF k).valuationSubring :=
  higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves
    (equalCharacteristicCompletedUnramifiedCompleteDVF k)
    (equalCharacteristicCompletedUnramifiedFrobenius k).toRingEquiv
    (fun x => by
      change Valued.v x ≤ 1 ↔
        Valued.v (equalCharacteristicCompletedUnramifiedFrobenius k x) ≤ 1
      rw [equalCharacteristicCompletedUnramifiedFrobenius_valuation])

/-- The integer action has the same underlying coefficient Frobenius. -/
@[simp]
theorem equalCharacteristicCompletedUnramifiedFrobeniusIntegerEquiv_coe
    (k : Type w) [Field k] [Finite k]
    (x : (equalCharacteristicCompletedUnramifiedCompleteDVF k).valuationSubring) :
    ((equalCharacteristicCompletedUnramifiedFrobeniusIntegerEquiv k x) :
        equalCharacteristicCompletedUnramifiedField k) =
      equalCharacteristicCompletedUnramifiedFrobenius k
        (x : equalCharacteristicCompletedUnramifiedField k) :=
  rfl

/-- On power series, the integer restriction is coefficientwise Frobenius. -/
theorem equalCharacteristicCompletedUnramifiedFrobeniusIntegerEquiv_powerSeries
    (k : Type w) [Field k] [Finite k] (f : (AlgebraicClosure k)⟦X⟧) :
    equalCharacteristicCompletedUnramifiedFrobeniusIntegerEquiv k
        (powerSeriesEquivLaurentInteger (AlgebraicClosure k) f) =
      powerSeriesEquivLaurentInteger (AlgebraicClosure k)
        (equalCharacteristicPowerSeriesFrobenius k f) := by
  apply Subtype.ext
  exact equalCharacteristicCompletedUnramifiedFrobenius_algebraMap_powerSeries k f

private theorem isIntegral_semilinear_ringEquiv_iff
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (φ : R ≃+* R) (σ : A ≃+* A)
    (hcomp : (algebraMap R A).comp φ.toRingHom =
      σ.toRingHom.comp (algebraMap R A)) (x : A) :
    IsIntegral R x ↔ IsIntegral R (σ x) := by
  constructor
  · intro hx
    exact IsIntegral.map_of_comp_eq φ.toRingHom σ.toRingHom hcomp hx
  · intro hx
    have hcompInv : (algebraMap R A).comp φ.symm.toRingHom =
        σ.symm.toRingHom.comp (algebraMap R A) := by
      apply RingHom.ext
      intro b
      have hb := DFunLike.congr_fun hcomp (φ.symm b)
      change algebraMap R A (φ (φ.symm b)) =
        σ (algebraMap R A (φ.symm b)) at hb
      rw [φ.apply_symm_apply] at hb
      apply σ.injective
      change σ (algebraMap R A (φ.symm b)) = σ (σ.symm (algebraMap R A b))
      rw [σ.apply_symm_apply]
      exact hb.symm
    have hback := IsIntegral.map_of_comp_eq
      φ.symm.toRingHom σ.symm.toRingHom hcompInv hx
    change IsIntegral R (σ.symm (σ x)) at hback
    rwa [RingEquiv.symm_apply_apply] at hback

/-- Every completed lift preserves the selected valuation ring because
that ring is the actual integral closure of the coefficient valuation ring. -/
theorem equalCharacteristicCompletedFrobeniusLiftEquiv_mem_valuationSubring_iff
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ)
    (x : equalCharacteristicCompletedLevelField F n) :
    x ∈ (equalCharacteristicCompletedLevelCompleteDVF F n).valuation.valuationSubring ↔
      equalCharacteristicCompletedFrobeniusLiftEquiv F n a x ∈
        (equalCharacteristicCompletedLevelCompleteDVF F n).valuation.valuationSubring := by
  let base := equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField
  let target := equalCharacteristicCompletedLevelCompleteDVF F n
  let E := equalCharacteristicCompletedUnramifiedField F.residueField
  let L := equalCharacteristicCompletedLevelField F n
  let φ := equalCharacteristicCompletedUnramifiedFrobeniusIntegerEquiv F.residueField
  let σ := equalCharacteristicCompletedFrobeniusLiftEquiv F n a
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    equalCharacteristicCompletedLevelCompleteDVF_isIntegralClosure F n
  have hcomp : (algebraMap base.valuationSubring L).comp φ.toRingHom =
      σ.toRingHom.comp (algebraMap base.valuationSubring L) := by
    apply RingHom.ext
    intro b
    change algebraMap E L ((φ b : base.valuationSubring) : E) =
      σ (algebraMap E L (b : E))
    rw [show φ = equalCharacteristicCompletedUnramifiedFrobeniusIntegerEquiv
        F.residueField by rfl,
      equalCharacteristicCompletedUnramifiedFrobeniusIntegerEquiv_coe,
      show σ = equalCharacteristicCompletedFrobeniusLiftEquiv F n a by rfl,
      equalCharacteristicCompletedFrobeniusLiftEquiv_algebraMap]
  have hmem (y : L) :
      IsIntegral base.valuationSubring y ↔ y ∈ target.valuation.valuationSubring := by
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring) (R := base.valuationSubring) (B := L)).1 hy
      change target.valuation y ≤ 1
      rw [← hz]
      exact z.property
    · intro hy
      exact (IsIntegralClosure.isIntegral_iff
        (A := target.valuationSubring) (R := base.valuationSubring) (B := L)).2
        ⟨⟨y, hy⟩, rfl⟩
  exact (hmem x).symm.trans
    ((isIntegral_semilinear_ringEquiv_iff φ σ hcomp x).trans (hmem (σ x)))

/-- The completed Frobenius lift on the actual integral closure. -/
noncomputable def equalCharacteristicCompletedFrobeniusIntegerEquiv
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicCompletedLevelCompleteDVF F n).valuationSubring ≃+*
      (equalCharacteristicCompletedLevelCompleteDVF F n).valuationSubring :=
  higherPrincipalUnitGroup.valuationSubringRingEquivOfPreserves
    (equalCharacteristicCompletedLevelCompleteDVF F n)
    (equalCharacteristicCompletedFrobeniusLiftEquiv F n a)
    (equalCharacteristicCompletedFrobeniusLiftEquiv_mem_valuationSubring_iff F n a)

/-- Coercing the integral lift recovers the original field automorphism. -/
@[simp]
theorem equalCharacteristicCompletedFrobeniusIntegerEquiv_coe
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ)
    (x : (equalCharacteristicCompletedLevelCompleteDVF F n).valuationSubring) :
    ((equalCharacteristicCompletedFrobeniusIntegerEquiv F n a x) :
        equalCharacteristicCompletedLevelField F n) =
      equalCharacteristicCompletedFrobeniusLiftEquiv F n a
        (x : equalCharacteristicCompletedLevelField F n) :=
  rfl

/-- The inverse integer action retains the inverse ambient automorphism. -/
@[simp]
theorem equalCharacteristicCompletedFrobeniusIntegerEquiv_symm_coe
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ)
    (x : (equalCharacteristicCompletedLevelCompleteDVF F n).valuationSubring) :
    (((equalCharacteristicCompletedFrobeniusIntegerEquiv F n a).symm x) :
        equalCharacteristicCompletedLevelField F n) =
      (equalCharacteristicCompletedFrobeniusLiftEquiv F n a).symm
        (x : equalCharacteristicCompletedLevelField F n) := by
  apply (equalCharacteristicCompletedFrobeniusLiftEquiv F n a).injective
  rw [RingEquiv.apply_symm_apply]
  have h := congrArg Subtype.val
    ((equalCharacteristicCompletedFrobeniusIntegerEquiv F n a).apply_symm_apply x)
  exact h

/-- Integral coefficient inclusion intertwines the two actual Frobenius
actions. -/
theorem equalCharacteristicCompletedFrobeniusIntegerEquiv_integerMap
    (F : LocalField.{u, v} K) [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ)
    (x : (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).valuationSubring) :
    equalCharacteristicCompletedFrobeniusIntegerEquiv F n a
        (integerMap (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
          (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF x) =
      integerMap (equalCharacteristicCompletedUnramifiedCompleteDVF F.residueField).toDVF
        (equalCharacteristicCompletedLevelCompleteDVF F n).toDVF
        (equalCharacteristicCompletedUnramifiedFrobeniusIntegerEquiv F.residueField x) := by
  apply Subtype.ext
  exact equalCharacteristicCompletedFrobeniusLiftEquiv_algebraMap F n a
    (x : equalCharacteristicCompletedUnramifiedField F.residueField)

end EqualCharacteristic
end LubinTate
