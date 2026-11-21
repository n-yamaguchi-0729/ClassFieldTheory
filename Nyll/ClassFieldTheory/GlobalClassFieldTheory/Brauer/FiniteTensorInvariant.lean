/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.InvariantSum
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.TensorBrauerLocalization
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FundamentalClass

/-! # Prescribing an invariant in the actual completed tensor block -/

@[expose] public section

open CategoryTheory AlgebraicNumberTheory.Valuations ContinuousCohomology
open IsDedekindDomain NumberField
open GlobalClassFieldTheory.Reciprocity LocalClassFieldTheory LocalFieldTheory
open scoped NumberField TensorProduct ValuativeRel

noncomputable section
namespace ClassFieldTheory.Brauer

section LocalizedTensor

variable {K L B : Type} [Field K] [Field L] [Field B] [Algebra K L] [Algebra K B]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] scalarTensorUnitsAction

private theorem localizedTensorH2_card
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial) (w : AbsoluteValueExtension vK L)
    (e : vK.Completion ≃ₐ[K] B) [ValuativeRel vK.Completion]
    [IsNonarchimedeanLocalField vK.Completion] :
    let : Algebra vK.Completion (LocalizedCompletion vK w) := localizedCompletionBaseAlgebra vK w
    Nat.card (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) (B ⊗[K] L)ˣ) 2) =
      Module.finrank vK.Completion (LocalizedCompletion vK w) := by
  intro baseAlgebra
  let F := vK.Completion
  let M := LocalizedCompletion vK w
  let : FiniteDimensional F M := localizedCompletionFiniteDimensional vK hvK w
  let : IsGalois F M := localizedCompletionIsGalois vK w
  let i : M →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let t := (groupCohomology.functor ℤ Gal(L/K) 2).mapIso
    (tensorUnitsRepBaseAlgEquiv (L := L) e.symm)
  calc
    _ = Nat.card (continuousCohomology 2 (galoisUnitsRep F M)) :=
      Nat.card_congr
        (t.toLinearEquiv.toAddEquiv.trans (localTensorRelativeH2Equiv vK hvK w)).toEquiv
    _ = Nat.card (relativeBr (fundamentalClassStage F M i)) :=
      Nat.card_congr (fundamentalClassStageEquiv F M i).toEquiv
    _ = Module.finrank F (fundamentalClassStage F M i) :=
      relativeBr_natCard F (fundamentalClassStage F M i)
    _ = Module.finrank F M := i.equivFieldRange.toLinearEquiv.finrank_eq.symm

end LocalizedTensor

section Invariant

variable {K : Type} [Field K] [NumberField K]
  (E : Type) [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
  (v : HeightOneSpectrum (𝓞 K))

/-- The invariant of the actual finite tensor cohomology in the canonical adic completion. -/
def finiteTensorInvariant : finiteTensorH2OfExtension E v →+ AddCircle (1 : ℚ) :=
  (finitePlaceBrauerInvariantEquiv K v).toAddMonoidHom.comp (finiteTensorH2ToBrauerOfExtension E v)

/-- The tensor invariant and the original tensor-to-Brauer map have the same kernel. -/
theorem finiteTensorInvariant_injective : Function.Injective (finiteTensorInvariant E v) := by
  let e := finitePlaceBrauerInvariantEquiv K v
  let f := finiteTensorH2ToBrauerOfExtension E v
  have hf := finiteTensorH2ToBrauerOfExtension_injective E v
  change Function.Injective (e.toAddMonoidHom.comp f)
  exact e.injective.comp hf

end Invariant

variable {K : Type} [Field K] [NumberField K]
  (E : FiniteGaloisIntermediateField K (SeparableClosure K)) [NumberField E]
  (v : HeightOneSpectrum (𝓞 K))

local notation "F" => ChosenFinitePlaceBaseCompletion (K := K) v
local notation "M" => ChosenFinitePlaceLocalizedCompletion (K := K) (L := E) v
local instance : Algebra F M :=
  localizedCompletionBaseAlgebra (HeightOneSpectrum.adicAbv K v)
    (chosenFinitePlaceExtension (L := E) v)
/-- The degree of the original completed extension at the chosen finite place. -/
abbrev finiteTensorCompletedDegree := Module.finrank F M

local notation "d" => finiteTensorCompletedDegree E v

omit [NumberField ↥E.toIntermediateField] in
/-- The degree-two cohomology of the actual finite tensor block has order
equal to the degree of the chosen completed extension. -/
theorem finiteTensorH2_card : Nat.card (finiteTensorH2OfExtension (E : Type) v) = d := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := E) v
  let : ValuativeRel F := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField F := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  exact localizedTensorH2_card vK (RayClass.adicAbv_isNontrivial v) w
    (finitePlaceCompletionAlgEquiv v)

end ClassFieldTheory.Brauer
