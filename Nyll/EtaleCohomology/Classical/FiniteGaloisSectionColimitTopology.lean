/- 
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionColimitAction
public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Continuous absolute Galois action on geometric sections

Every section comes from a finite Galois extension, so its orbit map
factors through that finite Galois group. Thus the actual colimit action
has open stabilizers for the discrete topology on sections.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

variable (K : Type u) [Field K]
variable (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u})

section Discrete

variable [TopologicalSpace (finiteGaloisSectionColimit K F)]
  [DiscreteTopology (finiteGaloisSectionColimit K F)]

omit [DiscreteTopology (finiteGaloisSectionColimit K F)] in
/-- Every actual geometric section has a continuous absolute Galois orbit map. -/
theorem finiteGaloisSectionColimitAction_continuous_orbit
    (x : finiteGaloisSectionColimit K F) :
    Continuous (fun σ : Gal(AlgebraicClosure K/K) =>
      (finiteGaloisSectionColimitAction K F σ).asIso.hom x) := by
  obtain ⟨E, s, rfl⟩ := finiteGaloisSectionColimit_exists_stage K F x
  let g : Gal(E/K) → finiteGaloisSectionColimit K F :=
    fun τ => finiteGaloisSectionColimitι K F E ((fieldGaloisSheafAction K E F τ).asIso.hom s)
  have hg : Continuous g := continuous_of_discreteTopology
  have hr : Continuous (AlgEquiv.restrictNormalHom
      (F := K) (K₁ := AlgebraicClosure K) E) :=
    InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField
  apply (hg.comp hr).congr
  intro σ
  exact (ConcreteCategory.congr_hom
    (finiteGaloisSectionColimitAction_ι K F σ E) s).symm

/-- Stabilizers of actual geometric sections are open in the Krull topology. -/
theorem finiteGaloisSectionColimitAction_isOpen_stabilizer
    (x : finiteGaloisSectionColimit K F) :
    IsOpen {σ : Gal(AlgebraicClosure K/K) |
      (finiteGaloisSectionColimitAction K F σ).asIso.hom x = x} :=
  (isOpen_discrete ({x} : Set (finiteGaloisSectionColimit K F))).preimage
    (finiteGaloisSectionColimitAction_continuous_orbit K F x)

/-- The actual absolute Galois action is jointly continuous. -/
theorem finiteGaloisSectionColimitAction_continuous :
    Continuous (fun p : Gal(AlgebraicClosure K/K) × finiteGaloisSectionColimit K F =>
      (finiteGaloisSectionColimitAction K F p.1).asIso.hom p.2) :=
  continuous_prod_of_discrete_right.mpr
    (fun x => finiteGaloisSectionColimitAction_continuous_orbit K F x)

/-- The continuous-linear version of the actual absolute Galois action. -/
def finiteGaloisSectionColimitContRepresentation :
    ContRepresentation ℤ Gal(AlgebraicClosure K/K) (finiteGaloisSectionColimit K F) where
  toMonoidHom :=
    { toFun := fun σ =>
        { toLinearMap := (finiteGaloisSectionColimitRep K F).ρ σ
          cont := continuous_of_discreteTopology }
      map_one' := by
        apply ContinuousLinearMap.ext
        intro x
        exact congrArg (fun a => a.asIso.hom x)
          (map_one (finiteGaloisSectionColimitAction K F))
      map_mul' σ τ := by
        apply ContinuousLinearMap.ext
        intro x
        exact congrArg (fun a => a.asIso.hom x)
          (map_mul (finiteGaloisSectionColimitAction K F) σ τ) }

end Discrete

/-- The actual geometric-section coefficient object with its discrete topology. -/
def finiteGaloisSectionColimitTopRep : TopRep.{u} ℤ Gal(AlgebraicClosure K/K) :=
  let : TopologicalSpace (finiteGaloisSectionColimit K F) := ⊥
  have : DiscreteTopology (finiteGaloisSectionColimit K F) := ⟨rfl⟩
  TopRep.of (finiteGaloisSectionColimitContRepresentation K F)

end EtaleCohomology
