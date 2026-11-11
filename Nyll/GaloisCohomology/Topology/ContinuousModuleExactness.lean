/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousEquivariantTupleLifting
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologySequence

/-!
# Exact sequences of actual continuous cochains

For discrete coefficients with jointly continuous actions, pointwise short
exact coefficient sequences induce actual short exact sequences of the
module-valued continuous cochain complexes.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits

namespace TopRep

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual continuous homogeneous complex after forgetting its topology. -/
def continuousModuleComplexFunctor :
    TopRep.{u} ℤ G ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  homogeneousContinuousCochainsFunctor G ⋙
    (forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).mapHomologicalComplex
      (ComplexShape.up ℕ)

/-- The module-valued continuous cochain functor is additive. -/
instance continuousModuleComplexFunctor_additive [LocallyCompactSpace G] :
    (continuousModuleComplexFunctor G).Additive where
  map_add := by
    intro A B φ ψ
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h :
        ((homogeneousContinuousCochainsFunctor G).map (φ + ψ)).f n =
          ((homogeneousContinuousCochainsFunctor G).map φ).f n +
            ((homogeneousContinuousCochainsFunctor G).map ψ).f n :=
      congrArg
        (fun m : (homogeneousContinuousCochainsFunctor G).obj A ⟶
          (homogeneousContinuousCochainsFunctor G).obj B => m.f n)
        ((homogeneousContinuousCochainsFunctor G).map_add (f := φ) (g := ψ))
    exact ConcreteCategory.congr_hom h x

/-- Pointwise exact discrete coefficients give degreewise exact cochains. -/
theorem continuousModuleComplex_degree_exact [LocallyCompactSpace G]
    (S : ShortComplex (TopRep.{u} ℤ G)) [DiscreteTopology S.X₂]
    (hS : ∀ y : S.X₂, S.g y = 0 → ∃ x : S.X₁, S.f x = y)
    (hA : Continuous (fun p : G × S.X₁ => S.X₁.ρ p.1 p.2)) (n : ℕ) :
    ((S.map (continuousModuleComplexFunctor G)).map
      (HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) n)).Exact := by
  apply (ShortComplex.exact_iff_of_hasForget _).mpr
  intro z hz
  exact homogeneousCochains_map_exact G S.X₁ S.X₂ S.X₃
    S.f S.g hS hA n z hz

/-- Actual pointwise short exact discrete coefficients give an actual short
exact sequence of continuous cochain complexes. -/
theorem continuousModuleComplex_shortExact [LocallyCompactSpace G]
    (S : ShortComplex (TopRep.{u} ℤ G))
    [DiscreteTopology S.X₂] [DiscreteTopology S.X₃]
    (hf : Function.Injective S.f) (hg : Function.Surjective S.g)
    (hS : ∀ y : S.X₂, S.g y = 0 → ∃ x : S.X₁, S.f x = y)
    (hA : Continuous (fun p : G × S.X₁ => S.X₁.ρ p.1 p.2))
    (hB : Continuous (fun p : G × S.X₂ => S.X₂.ρ p.1 p.2)) :
    (S.map (continuousModuleComplexFunctor G)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine
    { exact := continuousModuleComplex_degree_exact G S hS hA n
      mono_f := ?_
      epi_g := ?_ }
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact homogeneousCochains_map_injective G S.X₁ S.X₂ S.f hf n
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact homogeneousCochains_map_surjective G S.X₂ S.X₃ S.g hg hB n

/-- Forgetting topology identifies actual continuous homology with the
homology of the module-valued continuous complex. -/
def continuousModuleHomologyIso (X : TopRep.{u} ℤ G) (n : ℕ) :
    ((continuousModuleComplexFunctor G).obj X).homology n ≅
      (forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).obj
        (continuousCohomology n X) :=
  ((homogeneousCochains X).sc n).mapHomologyIso
    (forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ))

/-- Actual continuous cohomology vanishing implies vanishing of the
corresponding module-valued homology object. -/
theorem continuousModuleComplex_isZero_of_cohomology_eq_zero
    (X : TopRep.{u} ℤ G) (n : ℕ)
    (h : ∀ x : continuousCohomology n X, x = 0) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology n) := by
  have hz : IsZero ((forget₂ (TopModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).obj
      (continuousCohomology n X)) := by
    rw [IsZero.iff_id_eq_zero]
    apply ConcreteCategory.hom_ext
    intro x
    exact h x
  exact IsZero.of_iso hz (continuousModuleHomologyIso G X n)

end TopRep
