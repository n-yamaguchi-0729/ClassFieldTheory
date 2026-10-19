/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicTransportedUpperRamification
import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
import Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LubinTateTransport
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra

/-!
# Towers of transported equal-characteristic Lubin--Tate levels

The explicit level fields form a tower inside the Laurent separable closure.
After transporting their base algebra to the target local field, the same
inclusions are target-field linear.  This file packages the resulting
restriction homomorphism and its compatibility with the unchanged
underlying Galois automorphisms.
-/



noncomputable section

open scoped LaurentSeries ValuativeRel

namespace LubinTate

open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate.EqualCharacteristic
open RamificationTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Restriction between two transported Lubin--Tate levels, viewed as
extensions of the target equal-characteristic local field. -/
noncomputable def
    equalCharacteristicTransportedLubinTateRestrictNormalHom
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    {m n : ℕ} (hmn : m ≤ n) :
    let F : LocalField K := equalCharacteristicTargetLocalField K
    let B : Type := F.residueField⸨X⸩
    let _ : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E : IntermediateField B (SeparableClosure B) :=
      equalCharacteristicLubinTateLevelField F m
    let L : IntermediateField B (SeparableClosure B) :=
      equalCharacteristicLubinTateLevelField F n
    let _ : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F m
    let _ : Algebra B L := equalCharacteristicLubinTateLevelAlgebra F n
    let _ : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p (hKp := hKp) ϖ hϖ m
    let _ : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p (hKp := hKp) ϖ hϖ n
    Gal(L / K) →* Gal(E / K) := by
  intro F B hKq E L hBE hBL hKE hKL
  have hEL : E ≤ L := equalCharacteristicLubinTateLevelField_mono F hmn
  have hGalois : IsGalois B E := equalCharacteristicLubinTateLevelField_isGalois F m
  let restrictB : Gal(L / B) →* Gal(E / B) :=
    intermediateFieldRestrictNormalHom E L hEL
  exact
    (equalCharacteristicTransportedLubinTateGaloisEquiv
        K p (hKp := hKp) ϖ hϖ m).toMonoidHom.comp
      (restrictB.comp
        (equalCharacteristicTransportedLubinTateGaloisEquiv
          K p (hKp := hKp) ϖ hϖ n).symm.toMonoidHom)

/-- Evaluation of transported restriction agrees in the common Laurent
separable closure with restricting the underlying automorphism. -/
theorem
    equalCharacteristicTransportedLubinTateRestrictNormalHom_apply_val
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    {m n : ℕ} (hmn : m ≤ n) :
    let F : LocalField K := equalCharacteristicTargetLocalField K
    let B : Type := F.residueField⸨X⸩
    let _ : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E : IntermediateField B (SeparableClosure B) :=
      equalCharacteristicLubinTateLevelField F m
    let L : IntermediateField B (SeparableClosure B) :=
      equalCharacteristicLubinTateLevelField F n
    let _ : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F m
    let _ : Algebra B L := equalCharacteristicLubinTateLevelAlgebra F n
    let _ : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p (hKp := hKp) ϖ hϖ m
    let _ : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p (hKp := hKp) ϖ hϖ n
    let hEL : E ≤ L := equalCharacteristicLubinTateLevelField_mono F hmn
    ∀ (σ : Gal(L / K)) (x : E),
      E.val
          (equalCharacteristicTransportedLubinTateRestrictNormalHom
            K p (hKp := hKp) ϖ hϖ hmn σ x) =
        L.val (σ (IntermediateField.inclusion hEL x)) := by
  intro F B hKq E L hBE hBL hKE hKL hEL σ x
  have hGalois : IsGalois B E := equalCharacteristicLubinTateLevelField_isGalois F m
  let restrictB : Gal(L / B) →* Gal(E / B) :=
    intermediateFieldRestrictNormalHom E L hEL
  let qE : Gal(E / B) ≃* Gal(E / K) :=
    equalCharacteristicTransportedLubinTateGaloisEquiv K p (hKp := hKp) ϖ hϖ m
  let qL : Gal(L / B) ≃* Gal(L / K) :=
    equalCharacteristicTransportedLubinTateGaloisEquiv K p (hKp := hKp) ϖ hϖ n
  have hrestrict :
      E.val (restrictB (qL.symm σ) x) =
        L.val (qL.symm σ (IntermediateField.inclusion hEL x)) :=
    intermediateFieldRestrictNormalHom_apply_val
      E L hEL (qL.symm σ) x
  have hqL :
      L.val (qL.symm σ (IntermediateField.inclusion hEL x)) =
        L.val (σ (IntermediateField.inclusion hEL x)) := by
    have h :=
      congrArg
        (fun τ : Gal(L / K) =>
          L.val (τ (IntermediateField.inclusion hEL x)))
        (qL.apply_symm_apply σ)
    have heval : qL (qL.symm σ) (IntermediateField.inclusion hEL x) =
        qL.symm σ (IntermediateField.inclusion hEL x) :=
      equalCharacteristicTransportedLubinTateGaloisEquiv_apply
        K p (hKp := hKp) ϖ hϖ n (qL.symm σ) (IntermediateField.inclusion hEL x)
    exact (congrArg L.val heval).symm.trans h
  change E.val (qE (restrictB (qL.symm σ)) x) =
    L.val (σ (IntermediateField.inclusion hEL x))
  have heval : qE (restrictB (qL.symm σ)) x = restrictB (qL.symm σ) x :=
    equalCharacteristicTransportedLubinTateGaloisEquiv_apply
      K p (hKp := hKp) ϖ hϖ m (restrictB (qL.symm σ)) x
  exact (congrArg E.val heval).trans (hrestrict.trans hqL)

/-- The Galois-group identifications at two levels commute with restriction
between those levels. -/
theorem
    equalCharacteristicTransportedLubinTateGaloisEquiv_restrict
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    {m n : ℕ} (hmn : m ≤ n) :
    let F : LocalField K := equalCharacteristicTargetLocalField K
    let B : Type := F.residueField⸨X⸩
    let _ : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E : IntermediateField B (SeparableClosure B) :=
      equalCharacteristicLubinTateLevelField F m
    let L : IntermediateField B (SeparableClosure B) :=
      equalCharacteristicLubinTateLevelField F n
    let _ : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F m
    let _ : Algebra B L := equalCharacteristicLubinTateLevelAlgebra F n
    let _ : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p (hKp := hKp) ϖ hϖ m
    let _ : Algebra K L :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p (hKp := hKp) ϖ hϖ n
    let hEL : E ≤ L := equalCharacteristicLubinTateLevelField_mono F hmn
    ∀ (σ : Gal(L / B)),
      equalCharacteristicTransportedLubinTateRestrictNormalHom
          K p (hKp := hKp) ϖ hϖ hmn
          (equalCharacteristicTransportedLubinTateGaloisEquiv K p (hKp := hKp) ϖ hϖ n σ) =
        equalCharacteristicTransportedLubinTateGaloisEquiv K p (hKp := hKp) ϖ hϖ m
          (intermediateFieldRestrictNormalHom E L hEL σ) := by
  intro F B hKq E L hBE hBL hKE hKL hEL σ
  have hGalois : IsGalois B E := equalCharacteristicLubinTateLevelField_isGalois F m
  let restrictB : Gal(L / B) →* Gal(E / B) :=
    intermediateFieldRestrictNormalHom E L hEL
  let qE : Gal(E / B) ≃* Gal(E / K) :=
    equalCharacteristicTransportedLubinTateGaloisEquiv K p (hKp := hKp) ϖ hϖ m
  let qL : Gal(L / B) ≃* Gal(L / K) :=
    equalCharacteristicTransportedLubinTateGaloisEquiv K p (hKp := hKp) ϖ hϖ n
  change qE (restrictB (qL.symm (qL σ))) = qE (restrictB σ)
  rw [qL.symm_apply_apply]

end LubinTate
