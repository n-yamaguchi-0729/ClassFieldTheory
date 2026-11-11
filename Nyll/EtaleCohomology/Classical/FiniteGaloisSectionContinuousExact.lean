/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.FiniteGaloisSectionContinuousFunctor
public import Nyll.EtaleCohomology.Classical.InjectiveGeometricSectionContinuousPrimitives
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness
public import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Nyll.GaloisCohomology.Topology.ContinuousEquivariantTupleLifting

/-!
# Exact continuous cochains of actual geometric sections

The homogeneous continuous cochain complex is an exact functor of an
actual etale coefficient sheaf. This is
proved from actual section-colimit exactness and normalized cochain lifts.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace EtaleCohomology

variable (K : Type u) [Field K]

/-- The module-valued complex of actual continuous geometric-section cochains. -/
def finiteGaloisSectionContinuousModuleComplexFunctor :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u} ⥤
      CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  finiteGaloisSectionColimitTopRepFunctor K ⋙
    TopRep.continuousModuleComplexFunctor Gal(AlgebraicClosure K/K)

/-- The module-valued continuous cochain complex is additive in coefficients. -/
instance finiteGaloisSectionContinuousModuleComplexFunctor_additive :
    (finiteGaloisSectionContinuousModuleComplexFunctor K).Additive := by
  dsimp only [finiteGaloisSectionContinuousModuleComplexFunctor]
  infer_instance

/-- Each degree of the actual continuous cochain complex preserves exact
coefficient sequences. -/
theorem finiteGaloisSectionContinuousModuleComplex_degree_exact
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.Exact) (n : ℕ) :
    ((S.map (finiteGaloisSectionContinuousModuleComplexFunctor K)).map
      (HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) n)).Exact := by
  apply (ShortComplex.exact_iff_of_hasForget _).mpr
  intro z hz
  have : DiscreteTopology (finiteGaloisSectionColimitTopRep K S.X₂) := ⟨rfl⟩
  have he := hS.map (finiteGaloisSectionColimitFunctor K)
  have hlift :
      ∀ y : finiteGaloisSectionColimitTopRep K S.X₂,
        finiteGaloisSectionColimitTopRepMap K S.g y = 0 →
        ∃ x : finiteGaloisSectionColimitTopRep K S.X₁,
          finiteGaloisSectionColimitTopRepMap K S.f x = y :=
    (ShortComplex.ab_exact_iff (S.map (finiteGaloisSectionColimitFunctor K))).mp he
  have hA : Continuous
      (fun p : Gal(AlgebraicClosure K/K) × finiteGaloisSectionColimitTopRep K S.X₁ =>
        (finiteGaloisSectionColimitTopRep K S.X₁).ρ p.1 p.2) := by
    let : TopologicalSpace (finiteGaloisSectionColimit K S.X₁) := ⊥
    have : DiscreteTopology (finiteGaloisSectionColimit K S.X₁) := ⟨rfl⟩
    exact finiteGaloisSectionColimitAction_continuous K S.X₁
  exact TopRep.homogeneousCochains_map_exact _ _ _ _
    (finiteGaloisSectionColimitTopRepMap K S.f)
    (finiteGaloisSectionColimitTopRepMap K S.g) hlift hA n z hz

/-- Exact coefficient sequences give exact sequences of actual continuous
cochain complexes. -/
theorem finiteGaloisSectionContinuousModuleComplex_exact
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.Exact) :
    (S.map (finiteGaloisSectionContinuousModuleComplexFunctor K)).Exact :=
  HomologicalComplex.exact_of_degreewise_exact _
    (finiteGaloisSectionContinuousModuleComplex_degree_exact K S hS)

/-- The module-valued continuous geometric-section complex is an exact functor. -/
instance finiteGaloisSectionContinuousModuleComplexFunctor_preservesHomology :
    (finiteGaloisSectionContinuousModuleComplexFunctor K).PreservesHomology :=
  ((Functor.exact_tfae (finiteGaloisSectionContinuousModuleComplexFunctor K)).out 2 3).mp
    (finiteGaloisSectionContinuousModuleComplex_exact K)

/-- Every actual short exact coefficient sequence gives a short exact sequence
of module-valued continuous geometric-section complexes. -/
theorem finiteGaloisSectionContinuousModuleComplex_shortExact
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact) :
    (S.map (finiteGaloisSectionContinuousModuleComplexFunctor K)).ShortExact :=
  by
    have : PreservesFiniteLimits (finiteGaloisSectionContinuousModuleComplexFunctor K) :=
      Functor.preservesFiniteLimits_of_preservesHomology _
    have : PreservesFiniteColimits (finiteGaloisSectionContinuousModuleComplexFunctor K) :=
      Functor.preservesFiniteColimits_of_preservesHomology _
    exact hS.map_of_exact (finiteGaloisSectionContinuousModuleComplexFunctor K)

/-- Injective actual etale sheaves have vanishing positive-degree cohomology
in the module-valued continuous geometric-section complex. -/
theorem finiteGaloisSectionContinuousModuleComplex_injective_isZero
    (I : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
    (n : ℕ) :
    IsZero (((finiteGaloisSectionContinuousModuleComplexFunctor K).obj I).homology (n + 1)) :=
  TopRep.continuousModuleComplex_isZero_of_cohomology_eq_zero
    Gal(AlgebraicClosure K/K) (finiteGaloisSectionColimitTopRep K I) (n + 1)
    (continuousCohomology_injective_geometricSections_eq_zero K I n)

/-- The actual connecting isomorphism for a short exact sequence with injective
middle sheaf, in every positive continuous-cohomology degree. -/
def finiteGaloisSectionContinuousDimensionShift
    (S : ShortComplex (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u}))
    (hS : S.ShortExact) [Injective S.X₂] (n : ℕ) :
    ((finiteGaloisSectionContinuousModuleComplexFunctor K).obj S.X₃).homology (n + 1) ≅
      ((finiteGaloisSectionContinuousModuleComplexFunctor K).obj S.X₁).homology (n + 2) :=
  (finiteGaloisSectionContinuousModuleComplex_shortExact K S hS).δIso
    (n + 1) (n + 2) rfl
    (finiteGaloisSectionContinuousModuleComplex_injective_isZero K S.X₂ n)
    (finiteGaloisSectionContinuousModuleComplex_injective_isZero K S.X₂ (n + 1))

end EtaleCohomology
