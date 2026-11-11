/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.DiscreteCoefficientQuotient
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness

/-!
# Exact continuous complexes for actual coefficient images

An injective coefficient morphism and the actual quotient by its image
give a short exact sequence of continuous homogeneous module complexes.
This also applies to submodule inclusions and invariant prime-order lines.
-/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory Limits ContRepresentation

namespace TopRep

section General
variable (R : Type v) [Ring R] [TopologicalSpace R] [DiscreteTopology R]
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : TopRep.{u} R G) (φ : A ⟶ B)

omit [DiscreteTopology R] [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The image of an equivariant coefficient map is invariant under the group action. -/
theorem coefficientMapRange_invariant (g : G) :
    LinearMap.range φ.hom.toContinuousLinearMap.toLinearMap ≤
      (LinearMap.range φ.hom.toContinuousLinearMap.toLinearMap).comap
        (B.ρ g).toLinearMap := by
  rintro b ⟨a, rfl⟩
  exact ⟨A.ρ g a, φ.hom.isIntertwining g a⟩

/-- The actual coefficient morphism followed by the quotient by its image. -/
def coefficientRangeShortComplex [DiscreteTopology B] :
    ShortComplex (TopRep.{u} R G) := by
  let W := LinearMap.range φ.hom.toContinuousLinearMap.toLinearMap
  let hW := coefficientMapRange_invariant R G A B φ
  let Q := invariantCoefficientQuotient R G B W hW
  let q : B ⟶ Q := invariantCoefficientQuotientProjection R G B W hW
  exact ShortComplex.mk φ q (by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext (π₁ := A.ρ) (π₂ := Q.ρ)
    apply ContinuousLinearMap.ext
    intro a
    exact (invariantCoefficientQuotientProjection_eq_zero_iff
      R G B W hW (φ a)).mpr ⟨a, rfl⟩)

end General

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B : TopRep.{u} ℤ G) [DiscreteTopology B] (φ : A ⟶ B)

/-- An actual injective coefficient morphism and its quotient induce a
short exact sequence of continuous module complexes. -/
theorem coefficientRangeContinuousModule_shortExact [LocallyCompactSpace G]
    (hφ : Function.Injective φ)
    (hA : Continuous (fun ga : G × A => A.ρ ga.1 ga.2))
    (hB : Continuous (fun gb : G × B => B.ρ gb.1 gb.2)) :
    ((coefficientRangeShortComplex ℤ G A B φ).map
      (continuousModuleComplexFunctor G)).ShortExact := by
  let : Module ℤ A := A.hV2
  let : Module ℤ B := B.hV2
  let W := LinearMap.range φ.hom.toContinuousLinearMap.toLinearMap
  let hW := coefficientMapRange_invariant ℤ G A B φ
  let S := coefficientRangeShortComplex ℤ G A B φ
  have : DiscreteTopology S.X₂ := inferInstanceAs (DiscreteTopology B)
  have : DiscreteTopology S.X₃ := invariantCoefficientQuotient_discrete ℤ G B W hW
  apply continuousModuleComplex_shortExact G S
  · exact hφ
  · exact invariantCoefficientQuotientProjection_surjective ℤ G B W hW
  · intro b hb
    exact (invariantCoefficientQuotientProjection_eq_zero_iff ℤ G B W hW b).mp hb
  · exact hA
  · exact hB

end TopRep
