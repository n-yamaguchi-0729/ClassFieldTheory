/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LaurentPrincipalUnitTransport
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LubinTateTransport
public import Nyll.ValuedFieldTheory.Ramification.LocalField.BaseChange
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedLevel
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedPrimitiveAction
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedPolynomialEvaluation
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizerNormalization
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusBaseEquiv
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusContinuity
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldAlgebra
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldCoefficientDescent
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldDegree
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldGeneration
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPowerBasis
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPrimitive
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusLift
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedNorm
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectBracketAtCompletedLevel
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracket
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracketRecursion
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectTargetLevelEmbedding
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaAtCompletedLevel
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFirstIdentity
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFrobeniusFixed
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaIteration
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaSeries
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaAtCompletedLevel
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaLocalInverse
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.AmbientBracketAction
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.DivisionModuleEndomorphisms
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateEndomorphism
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.ContractingEquation
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaCoefficients
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaEvaluation
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaUniqueness
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.RealIndexSteps
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.Core

/-!
# Upper ramification groups on transported equal-characteristic levels

The explicit Lubin--Tate level field is unchanged when its Laurent-series
base algebra is transported to an arbitrary equal-characteristic local
field.  The normalized Laurent equivalence preserves the valuation rings,
so the general base-field transport theorem identifies the two upper
ramification filtrations.
-/



@[expose] public section

noncomputable section

universe u v w

open scoped LaurentSeries ValuativeRel

namespace LubinTate

open LocalFieldTheory
open RamificationTheory.LocalField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate.EqualCharacteristic

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The two algebra maps from the Laurent model and the target local field
to a transported Lubin--Tate level have the same image. -/
theorem equalCharacteristicTransportedLubinTate_algebraMap_compat
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
    let F : LocalField K := equalCharacteristicTargetLocalField K
    let B : Type u := F.residueField⸨X⸩
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
    let B : Type u := F.residueField⸨X⸩
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
    let B : Type u := F.residueField⸨X⸩
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
    let B : Type u := F.residueField⸨X⸩
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
