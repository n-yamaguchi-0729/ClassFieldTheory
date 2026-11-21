/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.ContinuousUnramified
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.CyclicIntegralCarry
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.EmbeddedCorestriction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Brauer.FundamentalClass
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin

/-! # The cyclic Brauer invariant and the local reciprocity symbol -/

@[expose] public section

open LocalFieldTheory (localNormSubgroup)

noncomputable section

open CategoryTheory LocalClassFieldTheory LocalFieldTheory Module
open ClassFieldTower.Cohomology LocalFieldTheory.IsNonarchimedeanLocalField
open scoped ValuativeRel

namespace ClassFieldTheory.Brauer

universe u

/-- The scalar structure induced by the given finite Galois subfield. -/
@[reducible] def finiteGaloisStageAlgebra {F : Type u} [Field F]
    (D : FiniteGaloisIntermediateField F (SeparableClosure F)) :
    Algebra F (↥D.toIntermediateField) := D.toIntermediateField.toSubalgebra.algebra

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (E : FiniteGaloisIntermediateField K (SeparableClosure K))
  [IsCyclic Gal(E/K)] [IsAbelianGalois K E]
  (g : Gal(E/K)) (hg : ∀ x : Gal(E/K), x ∈ Subgroup.zpowers g)

private theorem cyclicBrauerClass_eq_of_artin_eq (a b : Kˣ)
    (h : LocalClassFieldTheory.abelianLocalArtinMap K E a =
      LocalClassFieldTheory.abelianLocalArtinMap K E b) :
    cyclicBrauerClass E g hg a = cyclicBrauerClass E g hg b := by
  let e := continuousRelativeUnitsH2Equiv K E
  change finiteInflation E (e.symm (cyclicUnitClass K E g hg (Additive.ofMul a))) =
    finiteInflation E (e.symm (cyclicUnitClass K E g hg (Additive.ofMul b)))
  apply congrArg (fun x => finiteInflation E (e.symm x))
  rw [← sub_eq_zero, ← map_sub]
  change cyclicUnitClass K E g hg (Additive.ofMul (a / b)) = 0
  apply (cyclicUnitClass_eq_zero_iff_norm K E g hg _).2
  rw [← LocalClassFieldTheory.abelianLocalArtinMap_ker K E, MonoidHom.mem_ker]
  change LocalClassFieldTheory.abelianLocalArtinMap K E (a / b) = 1
  rw [map_div, h, div_self']

private theorem integralRestriction_composite_finiteIntegralCarry_factors
    {G H J J₀ : Type u} [Group G] [Group H] [Group J] [Group J₀]
    [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace J] [TopologicalSpace J₀]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup J] [IsTopologicalGroup J₀]
    [DiscreteTopology G] [DiscreteTopology H] [Fintype G] [Fintype H] [IsCyclic G] [IsCyclic H]
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (h : H) (hh : ∀ x : H, x ∈ Subgroup.zpowers h)
    (r : J₀ →ₜ* G) (s : J →ₜ* H) (i : J →ₜ* J₀) (e : H ≃* G)
    (he : e h = g) (hrs : ∀ x : J, r (i x) = e (s x)) :
    integralRestriction i (integralRestriction r (finiteIntegralCarry g hg)) =
      integralRestriction s (finiteIntegralCarry h hh) :=
  (integralRestriction_comp_apply r i (finiteIntegralCarry g hg)).trans
    (integralRestriction_finiteIntegralCarry_factors g hg h hh (r.comp i) s e he hrs)

private def absoluteIntegralCarry {B : Type u} [Field B]
    (L : FiniteGaloisIntermediateField B (SeparableClosure B)) [IsCyclic Gal(L/B)]
    (σ : Gal(L/B)) (hσ : ∀ x : Gal(L/B), x ∈ Subgroup.zpowers σ) :
    continuousCohomology 2 (trivialIntegralTopRep Gal(SeparableClosure B/B)) :=
  integralRestriction (finiteGaloisRestriction L) (finiteIntegralCarry σ hσ)

private theorem cyclicBrauerClass_eq_absoluteIntegralCarry {B : Type u} [Field B]
    (L : FiniteGaloisIntermediateField B (SeparableClosure B)) [IsCyclic Gal(L/B)]
    (σ : Gal(L/B)) (hσ : ∀ x : Gal(L/B), x ∈ Subgroup.zpowers σ) (b : Bˣ) :
    cyclicBrauerClass L σ hσ b = unitsIntegralClass B b (absoluteIntegralCarry L σ hσ) :=
  cyclicBrauerClass_eq_unitsIntegralClass L σ hσ b

private theorem unitsIntegralClass_factor_finite_quotients
    {B C : Type u} [Field B] [Field C]
    (E₀ : FiniteGaloisIntermediateField B (SeparableClosure B))
    (D₀ : FiniteGaloisIntermediateField C (SeparableClosure C))
    [IsCyclic Gal(E₀/B)] [IsCyclic Gal(D₀/C)]
    (g₀ : Gal(E₀/B)) (hg₀ : ∀ x : Gal(E₀/B), x ∈ Subgroup.zpowers g₀)
    (h₀ : Gal(D₀/C)) (hh₀ : ∀ x : Gal(D₀/C), x ∈ Subgroup.zpowers h₀)
    (i : Gal(SeparableClosure C/C) →ₜ* Gal(SeparableClosure B/B))
    (q : Gal(D₀/C) ≃* Gal(E₀/B)) (hgen : q h₀ = g₀)
    (hf : ∀ σ, finiteGaloisRestriction E₀ (i σ) = q (finiteGaloisRestriction D₀ σ))
    (b : Cˣ) :
    unitsIntegralClass C b (absoluteIntegralCarry D₀ h₀ hh₀) =
      unitsIntegralClassAfterRestriction i b (absoluteIntegralCarry E₀ g₀ hg₀) := by
  let r : Gal(SeparableClosure B/B) →ₜ* Gal(E₀/B) := finiteGaloisRestriction E₀
  let t : Gal(SeparableClosure C/C) →ₜ* Gal(D₀/C) := finiteGaloisRestriction D₀
  let : DiscreteTopology Gal(E₀/B) := krullTopology_discreteTopology_of_finiteDimensional B E₀
  let : DiscreteTopology Gal(D₀/C) := krullTopology_discreteTopology_of_finiteDimensional C D₀
  have hh := integralRestriction_composite_finiteIntegralCarry_factors
    g₀ hg₀ h₀ hh₀ r t i q hgen hf
  have hmap := unitsIntegralClassAfterRestriction_apply i b (absoluteIntegralCarry E₀ g₀ hg₀)
  exact (congrArg (unitsIntegralClass C b) hh.symm).trans hmap.symm

section UnramifiedComparison

variable (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]

attribute [local instance] stageSeparableClosureAlgebra

@[reducible] local instance corestrictionStageAlgebra
    (D : FiniteGaloisIntermediateField F (SeparableClosure F)) :
    Algebra (↥F) (↥D.toIntermediateField) := finiteGaloisStageAlgebra D

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [IsAbelianGalois K ↥E.toIntermediateField] [FiniteDimensional K ↥F] in
private theorem cyclicUnitsIntegralClass_factored_embedded
    (D : FiniteGaloisIntermediateField (↥F) (SeparableClosure (↥F)))
    [IsCyclic Gal(↥D.toIntermediateField/↥F)]
    (j : SeparableClosure K ≃ₐ[F] SeparableClosure F)
    (p : Gal(↥D.toIntermediateField/↥F) ≃* Gal(E/K))
    (h : Gal(↥D.toIntermediateField/↥F)) (hh : ∀ x, x ∈ Subgroup.zpowers h)
    (hgen : p h = g)
    (hp : ∀ σ, finiteGaloisRestriction E (embeddedAbsoluteRestrictionHom K F j σ) =
      p (finiteGaloisRestriction D σ))
    (b : Fˣ) :
    unitsIntegralClass (↥F) b (absoluteIntegralCarry D h hh) =
      embeddedUnitsIntegralClass K F j b (absoluteIntegralCarry E g hg) := by
  let i := embeddedAbsoluteRestrictionHom K F j
  with_reducible_and_instances
    exact unitsIntegralClass_factor_finite_quotients E D g hg h hh i p hgen hp b


omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [IsAbelianGalois K ↥E.toIntermediateField] in
/-- Corestriction carries the cyclic class over a factored absolute action to
the cyclic class of the norm of the same coefficient unit. -/
private theorem cyclicBrauerClass_embeddedCorestriction_of_restriction
    (D : FiniteGaloisIntermediateField (↥F) (SeparableClosure (↥F)))
    [IsCyclic Gal(↥D.toIntermediateField/↥F)]
    (j : SeparableClosure K ≃ₐ[F] SeparableClosure F)
    (p : Gal(↥D.toIntermediateField/↥F) ≃* Gal(E/K))
    (h : Gal(↥D.toIntermediateField/↥F)) (hh : ∀ x, x ∈ Subgroup.zpowers h)
    (hgen : p h = g)
    (hp : ∀ σ, finiteGaloisRestriction E (embeddedAbsoluteRestrictionHom K F j σ) =
      p (finiteGaloisRestriction D σ))
    (b : Fˣ) :
    embeddedAbsoluteBrCorestriction K F j (cyclicBrauerClass D h hh b) =
      cyclicBrauerClass E g hg (normUnits K F b) := by
  let c := embeddedAbsoluteBrCorestriction K F j
  have hD := cyclicBrauerClass_eq_absoluteIntegralCarry D h hh b
  have hUnit := cyclicUnitsIntegralClass_factored_embedded K E g hg F D j p h hh hgen hp b
  have hCor := embeddedAbsoluteBrCorestriction_unitsIntegralClass K F j b
    (absoluteIntegralCarry E g hg)
  have hE := cyclicBrauerClass_eq_absoluteIntegralCarry E g hg (normUnits K F b)
  exact (congrArg c (hD.trans hUnit)).trans (hCor.trans hE.symm)

attribute [local instance] embeddedStageSpectralNormedField embeddedStageSpectralValuativeRel
  embeddedStageSpectralLocalField

/-- The cyclic invariant equals that of the compatible unramified class carrying the unit norm. -/
theorem cyclicInvariant_eq_of_unramified_comparison
    (D : FiniteGaloisIntermediateField (↥F) (SeparableClosure (↥F)))
    [IsCyclic Gal(↥D.toIntermediateField/↥F)]
    (j : SeparableClosure K ≃ₐ[F] SeparableClosure F)
    (p : Gal(↥D.toIntermediateField/↥F) ≃* Gal(E/K))
    (h : Gal(↥D.toIntermediateField/↥F)) (hh : ∀ x, x ∈ Subgroup.zpowers h)
    (hgen : p h = g)
    (hp : ∀ σ, finiteGaloisRestriction E (embeddedAbsoluteRestrictionHom K F j σ) =
      p (finiteGaloisRestriction D σ))
    (a : Kˣ) (b : Fˣ)
    (hnorm : abelianLocalArtinMap K E (normUnits K F b) = abelianLocalArtinMap K E a)
    {value : AddCircle (1 : ℚ)}
    (hvalue : localBrauerInvariant F (cyclicBrauerClass D h hh b) = value) :
    localBrauerInvariant K (cyclicBrauerClass E g hg a) = value := by
  let vK := localBrauerInvariant K
  let c := embeddedAbsoluteBrCorestriction K F j
  let y := cyclicBrauerClass D h hh b
  have hcor : c y = cyclicBrauerClass E g hg (normUnits K F b) :=
    cyclicBrauerClass_embeddedCorestriction_of_restriction K E g hg F D j p h hh hgen hp b
  have hClass := cyclicBrauerClass_eq_of_artin_eq K E g hg a (normUnits K F b) hnorm.symm
  calc
    _ = vK (c y) := congrArg vK (hClass.trans hcor.symm)
    _ = localBrauerInvariant F y := localBrauerInvariant_embeddedCorestriction K F j y
    _ = _ := hvalue

end UnramifiedComparison

end ClassFieldTheory.Brauer
