/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LaurentPrincipalUnitTransport
import Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LubinTateTransport
import Nyll.ValuedFieldTheory.Ramification.LocalField.BaseChange
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedLevel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedPrimitiveAction
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedPolynomialEvaluation
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizerNormalization
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusBaseEquiv
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusContinuity
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldAlgebra
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldCoefficientDescent
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldDegree
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldGeneration
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPowerBasis
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPrimitive
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusLift
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedNorm
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectBracketAtCompletedLevel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracket
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracketRecursion
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectTargetLevelEmbedding
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaAtCompletedLevel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFirstIdentity
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFrobeniusFixed
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaIteration
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaSeries
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaAtCompletedLevel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaLocalInverse
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.AmbientBracketAction
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.DivisionModuleEndomorphisms
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateEndomorphism
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.ContractingEquation
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaCoefficients
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaEvaluation
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaUniqueness
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.RealIndexSteps
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.Core

/-!
# Upper ramification groups on transported equal-characteristic levels

The explicit Lubin--Tate level field is unchanged when its Laurent-series
base algebra is transported to an arbitrary equal-characteristic local
field.  The normalized Laurent equivalence preserves the valuation rings,
so the general base-field transport theorem identifies the two upper
ramification filtrations.
-/



noncomputable section

open scoped LaurentSeries ValuativeRel

namespace LubinTate

open LocalFieldTheory
open RamificationTheory.LocalField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate.EqualCharacteristic

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The two algebra maps from the Laurent model and the target local field
to a transported Lubin--Tate level have the same image. -/
theorem equalCharacteristicTransportedLubinTate_algebraMap_compat
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
    let F : LocalField K := equalCharacteristicTargetLocalField K
    let B : Type := F.residueField⸨X⸩
    let _ : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E : IntermediateField B (SeparableClosure B) :=
      equalCharacteristicLubinTateLevelField F n
    let _ : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F n
    let _ : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p (hKp := hKp) ϖ hϖ n
    let _ : CharP K p := hKp
    ∀ (x : B),
      algebraMap K E
          (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ x) =
        algebraMap B E x := by
  intro F B hKq E hBE hKE hCharP x
  exact DFunLike.congr_fun
    (equalCharacteristicTransportedLubinTateLevelAlgebra_comp
      K p (hKp := hKp) ϖ hϖ n) x

/-- Identification of the Galois group over the Laurent base with the
Galois group for the transported target-field algebra. It leaves every
underlying automorphism of the level field unchanged. -/
noncomputable def equalCharacteristicTransportedLubinTateGaloisEquiv
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
    let F : LocalField K := equalCharacteristicTargetLocalField K
    let B : Type := F.residueField⸨X⸩
    let _ : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E : IntermediateField B (SeparableClosure B) :=
      equalCharacteristicLubinTateLevelField F n
    let _ : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F n
    let _ : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p (hKp := hKp) ϖ hϖ n
    Gal(E / B) ≃* Gal(E / K) := by
  intro F B hKq E hBE hKE
  let : CharP K p := hKp
  exact galoisGroupEquivOfBaseRingEquiv B K E
    (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ)
    (equalCharacteristicTransportedLubinTate_algebraMap_compat
      K p (hKp := hKp) ϖ hϖ n)

@[simp]
theorem equalCharacteristicTransportedLubinTateGaloisEquiv_apply
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
    let F : LocalField K := equalCharacteristicTargetLocalField K
    let B : Type := F.residueField⸨X⸩
    let _ : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E : IntermediateField B (SeparableClosure B) :=
      equalCharacteristicLubinTateLevelField F n
    let _ : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F n
    let _ : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p (hKp := hKp) ϖ hϖ n
    ∀ (σ : Gal(E / B)) (x : E),
      equalCharacteristicTransportedLubinTateGaloisEquiv
          K p (hKp := hKp) ϖ hϖ n σ x =
        σ x := by
  intro F B hKq E hBE hKE σ x
  let : CharP K p := hKp
  exact galoisGroupEquivOfBaseRingEquiv_apply B K E
    (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ)
    (equalCharacteristicTransportedLubinTate_algebraMap_compat
      K p (hKp := hKp) ϖ hϖ n) σ x

/-- The normalized base-field equivalence transports the canonical local
upper ramification group on every explicit Lubin--Tate level. -/
theorem equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) :
    let F : LocalField K := equalCharacteristicTargetLocalField K
    let B : Type := F.residueField⸨X⸩
    let _ : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E : IntermediateField B (SeparableClosure B) :=
      equalCharacteristicLubinTateLevelField F n
    let _ : Algebra B E := equalCharacteristicLubinTateLevelAlgebra F n
    let _ : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p (hKp := hKp) ϖ hϖ n
    let _ : ValuativeRel B := equalCharacteristicLaurentValuativeRel F
    let _ : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    let _ : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    let _ : IsGalois B E := equalCharacteristicLubinTateLevelField_isGalois F n
    let _ : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p (hKp := hKp) ϖ hϖ n
    let _ : IsGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K p (hKp := hKp) ϖ hϖ n
    Subgroup.map
        (equalCharacteristicTransportedLubinTateGaloisEquiv
          K p (hKp := hKp) ϖ hϖ n).toMonoidHom
        (localUpperRamificationGroup B E t) =
      localUpperRamificationGroup K E t := by
  intro F B hKq E hBE hKE hBRel hBLocal hFiniteBE hGaloisBE hFiniteKE hGaloisKE
  let : CharP K p := hKp
  exact localUpperRamificationGroup_map_baseRingEquiv B K E
    (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ)
    (equalCharacteristicTransportedLubinTate_algebraMap_compat
      K p (hKp := hKp) ϖ hϖ n)
    (equalCharacteristicTargetLaurentRingEquiv_val_le_one_iff K p ϖ hϖ) t

end LubinTate
