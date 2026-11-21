/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.IdeleClassPGroupH1
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.StandardIdeleClassRepresentation
public import Nyll.GaloisCohomology.Cyclic.IntegralTateInflation
public import Nyll.GaloisCohomology.Cyclic.IntegralTatePSubgroups
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology

/-!
# Vanishing of the first cohomology of idèle classes

Restriction to a subgroup of prime-power order gives the actual idèle class
module of the top field over its fixed field. Sylow restriction then detects
vanishing for the whole Galois group.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ClassFieldTower.Martinet.Shafarevich IntegralGroupCohomology.Universe
open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Cohomology

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- First cohomology of the standard idele classes vanishes in every
finite Galois extension by detection on Sylow subgroups. -/
theorem standardIdeleClassH1_subsingleton :
    Subsingleton (groupCohomology.H1 (standardIdeleClassRep K L)) := by
  let A := standardIdeleClassRep K L
  have hSylow : TateVanishingOnPSubgroups A 1 := by
    intro p _ S hS
    let : Fintype S := Fintype.ofFinite S
    let M := IntermediateField.fixedField S
    let : NumberField M := NumberField.of_module_finite K M
    let : FiniteDimensional M L := Module.Finite.of_restrictScalars_finite K M L
    let : IsGalois M L := IsGalois.tower_top_of_isGalois K M L
    let eS : S ≃* Gal(L/M) := IntermediateField.subgroupEquivAlgEquiv S
    let D := Rep.res S.subtype A
    let B := standardIdeleClassRep M L
    let : Module ℤ D := D.hV2
    let : Module ℤ B := B.hV2
    let eC : D ≃ₗ[ℤ] B :=
      (AddEquiv.refl (Additive (NumberField.IdeleClassGroup (𝓞 L) L))).toIntLinearEquiv
    have he (σ : S) : eC.toLinearMap ∘ₗ D.ρ σ = B.ρ (eS σ) ∘ₗ eC.toLinearMap := by
      apply LinearMap.ext
      intro a
      have hσ : (eS σ).restrictScalars ℚ = (σ : Gal(L/K)).restrictScalars ℚ := by
        apply AlgEquiv.ext
        intro x
        rfl
      let c : Additive (NumberField.IdeleClassGroup (𝓞 L) L) := a
      change Additive.ofMul (NumberField.IdeleClassGroup.congr
        ((σ : Gal(L/K)).restrictScalars ℚ) c.toMul) =
        Additive.ofMul (NumberField.IdeleClassGroup.congr ((eS σ).restrictScalars ℚ) c.toMul)
      rw [hσ]
    let eH := groupCohomology.mapIso (A := B) (B := D) eS eC he 1
    let eT := tatePositiveIsoCohomology D 1 ≪≫ cohomologyIsoOriginal D 1
    let : Subsingleton (groupCohomology.H1 B) :=
      standardIdeleClassH1_subsingleton_of_isPGroup M L (hS.of_equiv eS)
    exact (ModuleCat.isZero_of_subsingleton (groupCohomology.H1 B)).of_iso (eT ≪≫ eH)
  let e := tatePositiveIsoCohomology A 1 ≪≫ cohomologyIsoOriginal A 1
  exact ModuleCat.subsingleton_of_isZero
    ((tate_isZero_of_vanishing_pSubgroups A 1 hSylow).of_iso e.symm)

end GlobalClassFieldTheory.Cohomology
