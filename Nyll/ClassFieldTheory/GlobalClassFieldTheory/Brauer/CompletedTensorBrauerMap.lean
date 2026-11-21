/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.EmbeddedInflation
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.InfinitePlaceModel
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.FinitePlaces
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.Localization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.LocalTensorShapiro

/-! # From actual tensor-unit cohomology to place Brauer classes -/

@[expose] public section

open CategoryTheory AlgebraicNumberTheory.Valuations ContinuousCohomology
open IsDedekindDomain LocalClassFieldTheory NumberField
open scoped NumberField TensorProduct

noncomputable section
namespace ClassFieldTheory.Brauer

section CompletedBase

variable {K L F : Type} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
  [FiniteDimensional K L] [IsGalois K L]
  (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) (w : AbsoluteValueExtension vK L)

local instance : MulDistribMulAction Gal(L/K) (F ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := F)

/-- Local tensor H² maps into the usual Brauer group of the completed base
by base transport, Shapiro, and actual local inflation. -/
def tensorH2ToCompletedBrauer (e : vK.Completion ≃ₐ[K] F) :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) (F ⊗[K] L)ˣ) 2 →+ Br F := by
  let M := LocalizedCompletion vK w
  let : Algebra vK.Completion M := localizedCompletionBaseAlgebra vK w
  let : FiniteDimensional vK.Completion M := localizedCompletionFiniteDimensional vK hvK w
  let : IsGalois vK.Completion M := localizedCompletionIsGalois vK w
  let t := (groupCohomology.functor ℤ (Gal(L/K)) 2).mapIso
    (tensorUnitsRepBaseAlgEquiv (L := L) e.symm)
  exact (embeddedRelativeToAbsolute (M := M) e).comp
    ((localTensorRelativeH2Equiv vK hvK w).toAddMonoidHom.comp t.hom.hom.toAddMonoidHom)

/-- The tensor cohomology map to the absolute local Brauer group is injective. -/
theorem tensorH2ToCompletedBrauer_injective (e : vK.Completion ≃ₐ[K] F) :
    Function.Injective (tensorH2ToCompletedBrauer vK hvK w e) := by
  let M := LocalizedCompletion vK w
  let : Algebra vK.Completion M := localizedCompletionBaseAlgebra vK w
  let : FiniteDimensional vK.Completion M := localizedCompletionFiniteDimensional vK hvK w
  let : IsGalois vK.Completion M := localizedCompletionIsGalois vK w
  let t := (groupCohomology.functor ℤ (Gal(L/K)) 2).mapIso
    (tensorUnitsRepBaseAlgEquiv (L := L) e.symm)
  exact (embeddedRelativeToAbsolute_injective (M := M) e).comp
    ((localTensorRelativeH2Equiv vK hvK w).injective.comp t.toLinearEquiv.injective)

end CompletedBase

section NumberFieldExtension

variable {K : Type} [Field K] [NumberField K]
  (L : Type) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local instance (F : Type) [Field F] [Algebra K F] :
    MulDistribMulAction Gal(L/K) (F ⊗[K] L)ˣ := scalarTensorUnitsAction

/-- Degree-two cohomology of units in the actual adic tensor product. -/
abbrev finiteTensorH2OfExtension (v : HeightOneSpectrum (𝓞 K)) :=
  groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) (v.adicCompletion K ⊗[K] L)ˣ) 2

/-- The actual finite tensor map for an arbitrary finite Galois top field. -/
def finiteTensorH2ToBrauerOfExtension (v : HeightOneSpectrum (𝓞 K)) :
    finiteTensorH2OfExtension L v →+ Br (v.adicCompletion K) :=
  tensorH2ToCompletedBrauer (HeightOneSpectrum.adicAbv K v) (RayClass.adicAbv_isNontrivial v)
    (chosenFinitePlaceExtension (L := L) v) (finitePlaceCompletionAlgEquiv v)

omit [NumberField L] in
theorem finiteTensorH2ToBrauerOfExtension_injective (v : HeightOneSpectrum (𝓞 K)) :
    Function.Injective (finiteTensorH2ToBrauerOfExtension L v) :=
  tensorH2ToCompletedBrauer_injective _ _ _ _

/-- The actual infinite tensor map for an arbitrary finite Galois top field. -/
def infiniteTensorH2ToBrauerOfExtension (v : InfinitePlace K) :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) (v.Completion ⊗[K] L)ˣ) 2 →+
      Br v.Completion :=
  tensorH2ToCompletedBrauer v.1 v.isNontrivial
    (infinitePlaceAbsoluteValueExtension v (chosenInfinitePlaceAbove (L := L) v)
      (chosenInfinitePlaceAbove_comap (L := L) v))
    (infinitePlaceCompletionAlgEquiv v).symm

omit [NumberField K] [NumberField L] in
theorem infiniteTensorH2ToBrauerOfExtension_injective (v : InfinitePlace K) :
    Function.Injective (infiniteTensorH2ToBrauerOfExtension L v) :=
  tensorH2ToCompletedBrauer_injective _ _ _ _

end NumberFieldExtension

variable {K : Type} [Field K] [NumberField K]
  (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]
  {F : Type} [Field F] [Algebra K F]

local instance : MulDistribMulAction Gal(E/K) (F ⊗[K] E)ˣ :=
  scalarTensorUnitsAction (K := K) (L := E) (A := F)

omit [NumberField K] [NumberField E] in
/-- The tensor diagonal, followed by local inflation, is the canonical
restriction of the original inflated global Brauer class. -/
theorem tensorH2ToCompletedBrauer_diagonal
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) (w : AbsoluteValueExtension vK E)
    (e : vK.Completion ≃ₐ[K] F) (x : relativeBr E) :
    tensorH2ToCompletedBrauer vK hvK w e
      (groupCohomology.map (MonoidHom.id (Gal(E/K)))
        (tensorDiagonalRepHom (K := K) (L := E) F) 2
          (discreteOriginalH2Equiv (galoisUnitsRep K E) x)) =
      restrict (algebraMap K F) (finiteInflation E x) := by
  obtain ⟨z, rfl⟩ := π_surjective (galoisUnitsRep K E) 2 x
  rw [discreteOriginalH2Equiv_π]
  let M := LocalizedCompletion vK w
  let : Algebra vK.Completion M := localizedCompletionBaseAlgebra vK w
  let : FiniteDimensional vK.Completion M := localizedCompletionFiniteDimensional vK hvK w
  let : IsGalois vK.Completion M := localizedCompletionIsGalois vK w
  let : Algebra K M := localizedCompletionGlobalAlgebra vK w
  let : IsScalarTower K vK.Completion M := localizedCompletionIsScalarTower vK w
  let t := (groupCohomology.functor ℤ (Gal(E/K)) 2).mapIso
    (tensorUnitsRepBaseAlgEquiv (L := E) e.symm)
  let a : groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2 :=
    groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K E)
      (dehomogenizeTwoOriginal (galoisUnitsRep K E) z)
  let dF := groupCohomology.map (MonoidHom.id (Gal(E/K)))
    (tensorDiagonalRepHom (K := K) (L := E) F) 2 a
  let dV := groupCohomology.map (MonoidHom.id (Gal(E/K)))
    (tensorDiagonalRepHom (K := K) (L := E) vK.Completion) 2 a
  let b := localizedFieldRelativeRestriction vK w (π (galoisUnitsRep K E) 2 z)
  let f := (embeddedRelativeToAbsolute (M := M) e).comp
    (localTensorRelativeH2Equiv vK hvK w).toAddMonoidHom
  have ht : t.hom dF = dV := tensorUnitsH2BaseAlgEquiv_diagonal e.symm a
  have hb : localTensorRelativeH2Equiv vK hvK w dV = b :=
    localTensorRelativeH2Equiv_diagonal vK hvK w z
  change f (t.hom dF) = _
  calc
    _ = f dV := congrArg f ht
    _ = embeddedRelativeToAbsolute (M := M) e b :=
      congrArg (embeddedRelativeToAbsolute (M := M) e) hb
    _ = _ := (restrict_finiteInflation_eq_embeddedRelativeRestriction E e
      (localizedCompletionToAlgHom vK w) (π (galoisUnitsRep K E) 2 z)).symm

end ClassFieldTheory.Brauer
