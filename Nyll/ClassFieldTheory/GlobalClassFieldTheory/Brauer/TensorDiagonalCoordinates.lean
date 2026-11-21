/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteLocalizedStage
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.InfiniteLocalizedStage
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.TensorBrauerLocalization

/-! # Local coordinates of the actual diagonal Brauer cocycle -/

@[expose] public section

noncomputable section

open AlgebraicNumberTheory.Valuations ContinuousCohomology IsDedekindDomain NumberField
open scoped NumberField TensorProduct

namespace ClassFieldTheory.Brauer

variable {K : Type} [Field K] [NumberField K]

/-- Vanishing in the canonical finite completion kills the original tensor-unit coordinate. -/
theorem finitePlaceTensorDiagonalH2_eq_zero_of_localization
    (v : HeightOneSpectrum (𝓞 K))
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]
    (z : cocycles (galoisUnitsRep K (↥E.toIntermediateField)) 2)
    (hz : finitePlaceRestriction K v
      (finiteInflation E (π (galoisUnitsRep K (↥E.toIntermediateField)) 2 z)) = 0) :
    groupCohomology.map (MonoidHom.id (Gal(↥E.toIntermediateField/K)))
      (tensorDiagonalRepHom (K := K) (L := ↥E.toIntermediateField) (v.adicCompletion K)) 2
      (groupCohomology.H2π (underlyingIntegerRep (galoisUnitsRep K (↥E.toIntermediateField)))
        (dehomogenizeTwoOriginal (galoisUnitsRep K (↥E.toIntermediateField)) z)) = 0 := by
  let x := π (galoisUnitsRep K E) 2 z
  let f := finiteTensorH2ToBrauerOfExtension (↥E.toIntermediateField) v
  let V := galoisUnitsRep K (↥E.toIntermediateField)
  let d := groupCohomology.map (A := underlyingIntegerRep V)
    (MonoidHom.id (Gal(↥E.toIntermediateField/K)))
    (tensorDiagonalRepHom (K := K) (L := ↥E.toIntermediateField) (v.adicCompletion K)) 2
  let c := groupCohomology.H2π (underlyingIntegerRep V) (dehomogenizeTwoOriginal V z)
  have hc : discreteOriginalH2Equiv V x = c := discreteOriginalH2Equiv_π V z
  have hx := finiteTensorH2ToBrauer_diagonal E v x
  have hf := finiteTensorH2ToBrauerOfExtension_injective (L := ↥E.toIntermediateField) v
  have hzero : f (d (discreteOriginalH2Equiv V x)) = 0 := hx.trans hz
  have h₀ : d (discreteOriginalH2Equiv V x) = 0 := hf (hzero.trans f.map_zero.symm)
  exact (congrArg (fun a => d a) hc.symm).trans h₀

omit [NumberField K] in
/-- Vanishing in the canonical infinite completion kills the archimedean tensor coordinate. -/
theorem infinitePlaceTensorDiagonalH2_eq_zero_of_localization
    (v : InfinitePlace K)
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]
    (z : cocycles (galoisUnitsRep K (↥E.toIntermediateField)) 2)
    (hz : infinitePlaceRestriction K v
      (finiteInflation E (π (galoisUnitsRep K (↥E.toIntermediateField)) 2 z)) = 0) :
    groupCohomology.map (MonoidHom.id (Gal(↥E.toIntermediateField/K)))
      (tensorDiagonalRepHom (K := K) (L := ↥E.toIntermediateField) v.Completion) 2
      (groupCohomology.H2π (underlyingIntegerRep (galoisUnitsRep K (↥E.toIntermediateField)))
        (dehomogenizeTwoOriginal (galoisUnitsRep K (↥E.toIntermediateField)) z)) = 0 := by
  let x := π (galoisUnitsRep K E) 2 z
  let f := infiniteTensorH2ToBrauerOfExtension (↥E.toIntermediateField) v
  let V := galoisUnitsRep K (↥E.toIntermediateField)
  let d := groupCohomology.map (A := underlyingIntegerRep V)
    (MonoidHom.id (Gal(↥E.toIntermediateField/K)))
    (tensorDiagonalRepHom (K := K) (L := ↥E.toIntermediateField) v.Completion) 2
  let c := groupCohomology.H2π (underlyingIntegerRep V) (dehomogenizeTwoOriginal V z)
  have hc : discreteOriginalH2Equiv V x = c := discreteOriginalH2Equiv_π V z
  have hx := infiniteTensorH2ToBrauer_diagonal E v x
  have hf := infiniteTensorH2ToBrauerOfExtension_injective (L := ↥E.toIntermediateField) v
  have hzero : f (d (discreteOriginalH2Equiv V x)) = 0 := hx.trans hz
  have h₀ : d (discreteOriginalH2Equiv V x) = 0 := hf (hzero.trans f.map_zero.symm)
  exact (congrArg (fun a => d a) hc.symm).trans h₀

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

omit [NumberField L] [FiniteDimensional K L] in
/-- A principal relative idele has the original diagonal in its finite tensor coordinate. -/
theorem finitePlaceTensorDiagonal_principal (v : HeightOneSpectrum (𝓞 K)) (x : Lˣ) :
    Additive.ofMul (RelativeIdeleGroup.finiteComponent (K := K) (L := L) v
      (RelativeIdeleGroup.principalIdele K L x)) =
      tensorDiagonalRepHom (v.adicCompletion K) (Additive.ofMul x) := by
  apply Additive.toMul.injective
  apply Units.ext
  change relativeAdeleFiniteComponent (K := K) (L := L) v
    ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] (x : L)) = 1 ⊗ₜ[K] (x : L)
  rw [relativeAdeleFiniteComponent_tmul]
  rfl

omit [NumberField L] [FiniteDimensional K L] in
/-- A principal relative idele has the original diagonal in its infinite tensor coordinate. -/
theorem infinitePlaceTensorDiagonal_principal (v : InfinitePlace K) (x : Lˣ) :
    Additive.ofMul (RelativeIdeleGroup.infiniteComponent (K := K) (L := L) v
      (RelativeIdeleGroup.principalIdele K L x)) =
      tensorDiagonalRepHom v.Completion (Additive.ofMul x) := by
  apply Additive.toMul.injective
  apply Units.ext
  change relativeAdeleInfiniteComponent (K := K) (L := L) v
    ((1 : NumberField.AdeleRing (𝓞 K) K) ⊗ₜ[K] (x : L)) = 1 ⊗ₜ[K] (x : L)
  rw [relativeAdeleInfiniteComponent_tmul]
  rfl

end ClassFieldTheory.Brauer
