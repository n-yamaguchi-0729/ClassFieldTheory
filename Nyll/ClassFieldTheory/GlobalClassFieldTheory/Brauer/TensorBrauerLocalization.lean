/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.AbsoluteTensorDiagonal

/-! # Brauer localization on the finite stages of the chosen global closure -/

@[expose] public section

open AlgebraicNumberTheory.Valuations ContinuousCohomology IsDedekindDomain NumberField
open LocalClassFieldTheory
open scoped NumberField TensorProduct

noncomputable section

namespace ClassFieldTheory.Brauer

attribute [local instance] scalarTensorUnitsAction

variable {K : Type} [Field K] [NumberField K]
  (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]

/-- The finite tensor cohomology map to the canonical adic Brauer group. -/
abbrev finiteTensorH2ToBrauer (v : HeightOneSpectrum (𝓞 K)) :=
  finiteTensorH2ToBrauerOfExtension (K := K) (L := ↥E.toIntermediateField) v

omit [NumberField E] in
/-- The finite tensor coordinate retains the original degree-two class. -/
theorem finiteTensorH2ToBrauer_injective (v : HeightOneSpectrum (𝓞 K)) :
    let L : Type := ↥E.toIntermediateField
    Function.Injective (finiteTensorH2ToBrauerOfExtension (K := K) (L := L) v) := by
  intro L
  exact finiteTensorH2ToBrauerOfExtension_injective (L := L) v

/-- The archimedean tensor cohomology map to the actual completion. -/
abbrev infiniteTensorH2ToBrauer (v : InfinitePlace K) :=
  infiniteTensorH2ToBrauerOfExtension (K := K) (L := ↥E.toIntermediateField) v

omit [NumberField K] [NumberField E] in
/-- The archimedean tensor coordinate retains the original degree-two class. -/
theorem infiniteTensorH2ToBrauer_injective (v : InfinitePlace K) :
    let L : Type := ↥E.toIntermediateField
    Function.Injective (infiniteTensorH2ToBrauerOfExtension (K := K) (L := L) v) := by
  intro L
  exact infiniteTensorH2ToBrauerOfExtension_injective (L := L) v

omit [NumberField K] [NumberField E] in
private theorem relativeInflationOfStageEmbedding (x : relativeBr E) :
    relativeInflationOfEmbedding E.toIntermediateField.val x = finiteInflation E x := by
  let i := E.toIntermediateField.val
  let r := embeddedGaloisRestriction (B := K) i
  let s := finiteGaloisRestriction E
  let f := galoisUnitsMap r i.toRingHom (embeddedGaloisRestriction_commutes i)
  let g := finiteInflationCoefficientMap E
  have hg (σ : Gal(SeparableClosure K/K)) : r σ = s σ := by
    apply AlgEquiv.ext
    intro a
    apply i.injective
    exact (embeddedGaloisRestriction_commutes i σ a).trans
      (finiteGaloisRestriction_commutes E σ a).symm
  have hc (a : galoisUnitsRep K E) : f a = g a := rfl
  exact CategoryTheory.ConcreteCategory.congr_hom (map_eq_of_values 2 f g hg hc) x

omit [NumberField E] in
/-- The finite map agrees with canonical absolute localization on diagonal classes. -/
theorem finiteTensorH2ToBrauer_diagonal (v : HeightOneSpectrum (𝓞 K)) (x : relativeBr E) :
    finiteTensorH2ToBrauerOfExtension (↥E.toIntermediateField) v
      ((groupCohomology.functor ℤ Gal(↥E.toIntermediateField/K) 2).map
        (tensorDiagonalRepHom (K := K) (L := ↥E.toIntermediateField) (v.adicCompletion K))
        (discreteOriginalH2Equiv (galoisUnitsRep K (↥E.toIntermediateField)) x)) =
      finitePlaceRestriction K v (finiteInflation E x) := by
  let i : (↥E.toIntermediateField) →ₐ[K] SeparableClosure K := E.toIntermediateField.val
  have h := finiteTensorH2ToBrauerOfExtension_diagonal i v x
  have he : relativeInflationOfEmbedding i x = finiteInflation E x :=
    relativeInflationOfStageEmbedding E x
  exact h.trans (congrArg (finitePlaceRestriction K v) he)

omit [NumberField K] [NumberField E] in
/-- The infinite map agrees with canonical absolute localization on diagonal classes. -/
theorem infiniteTensorH2ToBrauer_diagonal (v : InfinitePlace K) (x : relativeBr E) :
    infiniteTensorH2ToBrauerOfExtension (↥E.toIntermediateField) v
      ((groupCohomology.functor ℤ Gal(↥E.toIntermediateField/K) 2).map
        (tensorDiagonalRepHom (K := K) (L := ↥E.toIntermediateField) v.Completion)
        (discreteOriginalH2Equiv (galoisUnitsRep K (↥E.toIntermediateField)) x)) =
      infinitePlaceRestriction K v (finiteInflation E x) := by
  let i : (↥E.toIntermediateField) →ₐ[K] SeparableClosure K := E.toIntermediateField.val
  have h := infiniteTensorH2ToBrauerOfExtension_diagonal i v x
  have he : relativeInflationOfEmbedding i x = finiteInflation E x :=
    relativeInflationOfStageEmbedding E x
  exact h.trans (congrArg (infinitePlaceRestriction K v) he)

end ClassFieldTheory.Brauer
