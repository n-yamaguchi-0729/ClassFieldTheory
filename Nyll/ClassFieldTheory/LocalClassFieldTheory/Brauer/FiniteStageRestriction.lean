/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.Brauer.FiniteBaseChange
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.LocalInvariant

/-! # Restriction and inflation at a nested finite Galois stage -/

@[expose] public section

open CategoryTheory TopRep ContinuousCohomology
open ClassFieldTower.Cohomology LocalFieldTheory Module
open scoped ValuativeRel

noncomputable section

namespace ClassFieldTheory.Brauer

universe u

variable {K : Type u} [Field K]

attribute [local instance] stageSeparableClosureAlgebra

section RelativeBase

variable {F : Type u} [Field F] [Algebra K F]
  (T : FiniteGaloisIntermediateField K (SeparableClosure K))
  [Algebra F (↥T.toIntermediateField)] [IsScalarTower K F (↥T.toIntermediateField)]
  [FiniteDimensional F (↥T.toIntermediateField)] [IsGalois F (↥T.toIntermediateField)]

/-- Restrict an inflated class through the same finite stage over the intermediate base. -/
theorem finiteInflation_restriction_via_same_stage
    (q : Gal(SeparableClosure F/F) →ₜ* Gal(SeparableClosure K/K))
    (d : SeparableClosure K →+* SeparableClosure F)
    (hq : ∀ (σ : Gal(SeparableClosure F/F)) (a : SeparableClosure K), d (q σ a) = σ (d a))
    (i : (↥T.toIntermediateField) →ₐ[F] SeparableClosure F)
    (hi : ∀ a : ↥T.toIntermediateField, i a = d a.val) (x : relativeBr T) :
    restrictOfEmbedding q d hq (finiteInflation T x) =
      relativeInflationOfEmbedding i (relativeBaseRestriction K F (↥T.toIntermediateField) x) := by
  let N := ↥T.toIntermediateField
  let r : Gal(N/F) →ₜ* Gal(N/K) := relativeBaseRestrictionHom K F N
  let s : Gal(SeparableClosure F/F) →ₜ* Gal(N/F) := embeddedGaloisRestriction (B := F) i
  have hs (σ : Gal(SeparableClosure F/F)) (a : N) : i (s σ a) = σ (i a) :=
    embeddedGaloisRestriction_commutes (B := F) i σ a
  have hr (σ : Gal(N/F)) (a : N) : (RingHom.id N) (r σ a) = σ ((RingHom.id N) a) := rfl
  have hgroups (σ : Gal(SeparableClosure F/F)) :
      r (s σ) = finiteGaloisRestriction T (q σ) := by
    apply AlgEquiv.ext
    intro a
    apply i.injective
    calc
      i (r (s σ) a) = σ (i a) := hs σ a
      _ = σ (d a.val) := congrArg σ (hi a)
      _ = d (q σ a.val) := (hq σ a.val).symm
      _ = d (finiteGaloisRestriction T (q σ) a).val :=
        (congrArg d (finiteGaloisRestriction_commutes T (q σ) a)).symm
      _ = i (finiteGaloisRestriction T (q σ) a) := (hi _).symm
  obtain ⟨z, rfl⟩ := π_surjective (galoisUnitsRep K N) 2 x
  let f := galoisUnitsMap r (RingHom.id N) hr
  have hπ : relativeBaseRestriction K F N (π (galoisUnitsRep K N) 2 z) =
      π (galoisUnitsRep F N) 2 (cocyclesMap r f 2 z) :=
    ConcreteCategory.congr_hom (π_map r f 2) z
  have hfactor := restrictOfEmbedding_finiteInflation_eq_of_factor (A := F) (M := N)
    T q d hq r (RingHom.id N) hr s i.toRingHom hs hgroups hi z
  exact hfactor.trans (congrArg (relativeInflationOfEmbedding i) hπ.symm)

end RelativeBase

section FiniteTower

variable (E : IntermediateField K (SeparableClosure K))
  (T : FiniteGaloisIntermediateField K (SeparableClosure K)) (h : E ≤ T.toIntermediateField)

/-- The scalar inclusion of nested finite stages in the chosen closure. -/
abbrev nestedStageAlgebra : Algebra E (↥T.toIntermediateField) :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- The inclusion is compatible with the original ground field. -/
theorem nestedStageTower :
    let : Algebra E (↥T.toIntermediateField) := nestedStageAlgebra E T h
    IsScalarTower K E (↥T.toIntermediateField) := by
  intro algebraOwner
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The upper stage remains finite over the nested base. -/
theorem nestedStageFinite :
    let : Algebra E (↥T.toIntermediateField) := nestedStageAlgebra E T h
    FiniteDimensional E (↥T.toIntermediateField) := by
  intro algebraOwner
  let : IsScalarTower K E (↥T.toIntermediateField) := nestedStageTower E T h
  exact FiniteDimensional.right K E (↥T.toIntermediateField)

/-- The upper stage embedded by the chosen comparison of closures. -/
def nestedStageEmbedding (j : SeparableClosure K ≃ₐ[E] SeparableClosure E) :
    let : Algebra E (↥T.toIntermediateField) := nestedStageAlgebra E T h
    (↥T.toIntermediateField) →ₐ[E] SeparableClosure E := by
  intro algebraOwner
  exact {
    toRingHom := j.toRingEquiv.toRingHom.comp T.toIntermediateField.val.toRingHom
    commutes' := j.commutes }

/-- Inflate a relative class through the original inclusion into the chosen
separable closure of the intermediate base field. -/
def relativeStageAbsoluteInflation (j : SeparableClosure K ≃ₐ[E] SeparableClosure E) :
    let : Algebra E (↥T.toIntermediateField) := nestedStageAlgebra E T h
    continuousCohomology 2 (galoisUnitsRep E (↥T.toIntermediateField)) →+ Br E := by
  intro algebraOwner
  let : IsScalarTower K E (↥T.toIntermediateField) := nestedStageTower E T h
  let : FiniteDimensional E (↥T.toIntermediateField) := nestedStageFinite E T h
  let : IsGalois E (↥T.toIntermediateField) :=
    IsGalois.tower_top_of_isGalois K E (↥T.toIntermediateField)
  exact relativeInflationOfEmbedding (nestedStageEmbedding E T h j)

theorem relativeStageAbsoluteInflation_injective (j : SeparableClosure K ≃ₐ[E] SeparableClosure E) :
    Function.Injective (relativeStageAbsoluteInflation E T h j) := by
  let : Algebra E (↥T.toIntermediateField) := nestedStageAlgebra E T h
  let : IsScalarTower K E (↥T.toIntermediateField) := nestedStageTower E T h
  let : FiniteDimensional E (↥T.toIntermediateField) := nestedStageFinite E T h
  let : IsGalois E (↥T.toIntermediateField) :=
    IsGalois.tower_top_of_isGalois K E (↥T.toIntermediateField)
  exact embeddedInflation_injective (A := E) (B := E) (fun a => ⟨a, rfl⟩)
    (nestedStageEmbedding E T h j)

/-- The restriction of an inflated class is the inflation of its actual
finite relative restriction. -/
theorem embeddedAbsoluteBrRestriction_finiteInflation
    (j : SeparableClosure K ≃ₐ[E] SeparableClosure E) (x : relativeBr T) :
    let : Algebra E (↥T.toIntermediateField) := nestedStageAlgebra E T h
    let : IsScalarTower K E (↥T.toIntermediateField) := nestedStageTower E T h
    let : FiniteDimensional E (↥T.toIntermediateField) := nestedStageFinite E T h
    embeddedAbsoluteBrRestriction K E j (finiteInflation T x) =
      relativeStageAbsoluteInflation E T h j
        (relativeBaseRestriction K E (↥T.toIntermediateField) x) := by
  intro algebraOwner towerOwner finiteOwner
  let N := ↥T.toIntermediateField
  let : IsGalois E N := IsGalois.tower_top_of_isGalois K E N
  let i : N →ₐ[E] SeparableClosure E := nestedStageEmbedding E T h j
  exact finiteInflation_restriction_via_same_stage T (embeddedAbsoluteRestrictionHom K E j)
    j.toRingEquiv.toRingHom (embeddedAbsoluteRestrictionHom_commutes K E j) i (fun _ => rfl) x

end FiniteTower

end ClassFieldTheory.Brauer
