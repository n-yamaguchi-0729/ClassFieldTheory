/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives
public import Nyll.GaloisCohomology.Topology.DiscreteCoefficientQuotient
public import Nyll.GaloisCohomology.Topology.DiscreteOriginalH2

/-! # Naturality of the actual discrete degree-two comparison -/

@[expose] public section

open CategoryTheory TopRep ContRepresentation
open scoped ContRepresentation

noncomputable section
namespace ContinuousCohomology

section MapCongruence

universe u

variable {G H : Type u} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  {X : TopRep.{u} ℤ G} {Y : TopRep.{u} ℤ H}

/-- Continuous cohomology maps agree when their group and coefficient functions agree. -/
theorem map_eq_of_values (n : ℕ) {r s : H →ₜ* G}
    (φ : TopRep.res r.toMonoidHom X ⟶ Y) (ψ : TopRep.res s.toMonoidHom X ⟶ Y)
    (hr : ∀ g, r g = s g) (hφ : ∀ a : X, φ a = ψ a) :
    ContinuousCohomology.map r φ n = ContinuousCohomology.map s ψ n := by
  have hrs : r = s := ContinuousMonoidHom.ext hr
  subst s
  apply congrArg (fun f : TopRep.res r.toMonoidHom X ⟶ Y => ContinuousCohomology.map r f n)
  let U := TopRep.res r.toMonoidHom X
  let : Module ℤ U := U.hV2
  let : Module ℤ Y := Y.hV2
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext (π₁ := U.ρ) (π₂ := Y.ρ)
  exact ContinuousLinearMap.ext hφ

/-- Composing continuous cohomology maps uses the specified group and coefficient composites. -/
theorem map_comp_eq_apply {J : Type u} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    {Z : TopRep.{u} ℤ J} (r : H →ₜ* G) (s : J →ₜ* H) (t : J →ₜ* G)
    (f : TopRep.res r.toMonoidHom X ⟶ Y) (g : TopRep.res s.toMonoidHom Y ⟶ Z)
    (h : TopRep.res t.toMonoidHom X ⟶ Z) (hGroups : ∀ j, r (s j) = t j)
    (hCoeffs : ∀ x : X, g (f x) = h x) (n : ℕ) (x : continuousCohomology n X) :
    map s g n (map r f n x) = map t h n x := by
  let c : TopRep.res (r.comp s).toMonoidHom X ⟶ Z := (TopRep.resFunctor s.toMonoidHom).map f ≫ g
  have h₁ := map_comp r s f g n
  have h₂ := map_eq_of_values n c h hGroups hCoeffs
  exact ConcreteCategory.congr_hom (h₁.symm.trans h₂) x

/-- Cohomology over the same group maps a composite coefficient morphism by composition. -/
theorem map_id_comp_apply {Z : TopRep.{u} ℤ G} (A B : TopRep.{u} ℤ G)
    (f : A ⟶ B) (g : B ⟶ Z) (n : ℕ) (x : continuousCohomology n A) :
    map (ContinuousMonoidHom.id G) g n (map (ContinuousMonoidHom.id G) f n x) =
      map (ContinuousMonoidHom.id G) (f ≫ g) n x := by
  let i := ContinuousMonoidHom.id G
  exact map_comp_eq_apply i i i f g (f ≫ g) (fun _ => rfl) (fun _ => rfl) n x

end MapCongruence

variable {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H] [DiscreteTopology G] [DiscreteTopology H]
  {X : TopRep.{0} ℤ G} {Y : TopRep.{0} ℤ H}

/-- Continuous and ordinary restriction carry the same original class when
the group map and coefficient map agree on the original carriers. -/
theorem discreteOriginalH2Equiv_map (r : H →ₜ* G) (φ : TopRep.res r.toMonoidHom X ⟶ Y)
    (f : Rep.res r.toMonoidHom (underlyingIntegerRep X) ⟶ underlyingIntegerRep Y)
    (hf : ∀ a : X, φ a = f a) (x : continuousCohomology 2 X) :
    discreteOriginalH2Equiv Y (ContinuousCohomology.map r φ 2 x) =
      groupCohomology.map r.toMonoidHom f 2 (discreteOriginalH2Equiv X x) := by
  obtain ⟨z, rfl⟩ := π_surjective X 2 x
  have hclass : ContinuousCohomology.map r φ 2 (π X 2 z) =
      π Y 2 (cocyclesMap r φ 2 z) :=
    ConcreteCategory.congr_hom (π_map r φ 2) z
  rw [hclass, discreteOriginalH2Equiv_π, discreteOriginalH2Equiv_π,
    groupCohomology.H2π_comp_map_apply]
  apply congrArg (groupCohomology.H2π (underlyingIntegerRep Y))
  apply groupCohomology.cocycles₂_ext
  intro g h
  change dehomogenizeTwoOriginal Y (cocyclesMap r φ 2 z) (g, h) =
    f (dehomogenizeTwoOriginal X z (r g, r h))
  rw [dehomogenizeTwoOriginal_apply, dehomogenizeTwoOriginal_apply, mappedRelativeCocycle_apply,
    map_one, map_mul, hf]

/-- Give the given integer coefficient morphism its actual discrete topology. -/
def discreteTopRepMap {A : Rep ℤ G} {B : Rep ℤ H}
    (r : H →ₜ* G) (f : Rep.res r.toMonoidHom A ⟶ B) :
    TopRep.res r.toMonoidHom (TopRep.discreteCoefficientTopRep ℤ G A) ⟶
      TopRep.discreteCoefficientTopRep ℤ H B := by
  let D := TopRep.res r.toMonoidHom (TopRep.discreteCoefficientTopRep ℤ G A)
  let Y := TopRep.discreteCoefficientTopRep ℤ H B
  let : DiscreteTopology D := TopRep.discreteCoefficientTopRep_discrete ℤ G A
  let : Module ℤ D := D.hV2
  let : Module ℤ Y := Y.hV2
  let m : D →ₗ[ℤ] Y := f.hom.toLinearMap
  let α : D.ρ →ⁱL Y.ρ :=
    { toLinearMap := m
      cont := continuous_of_discreteTopology
      isIntertwining' := fun σ => by
        apply ContinuousLinearMap.ext
        intro a
        exact DFunLike.congr_fun (f.hom.isIntertwining' σ) a }
  exact ConcreteCategory.ofHom α

/-- The original discrete coefficient comparison is the identity on the carrier. -/
def discreteTopRepCoefficientEquiv (A : Rep ℤ G) :
    underlyingIntegerRep (TopRep.discreteCoefficientTopRep ℤ G A) ≃+ A :=
  AddEquiv.refl _

/-- Discrete TopRep cohomology compared directly with the input ordinary representation. -/
def discreteTopRepH2Equiv (A : Rep ℤ G) :
    continuousCohomology 2 (TopRep.discreteCoefficientTopRep ℤ G A) ≃+
      groupCohomology A 2 :=
  let X := TopRep.discreteCoefficientTopRep ℤ G A
  (discreteOriginalH2Equiv X).trans
    (groupCohomology.equivariantH2AddEquiv (MulEquiv.refl G)
      (discreteTopRepCoefficientEquiv A) (fun _ _ => rfl))

/-- The representative of a discrete original cohomology class in the
input ordinary representation. -/
def discreteTopRepOriginalTwoCocycle (A : Rep ℤ G)
    (z : cocycles (TopRep.discreteCoefficientTopRep ℤ G A) 2) : groupCohomology.cocycles₂ A :=
  groupCohomology.reindexTwoCocycle (MulEquiv.refl G) (discreteTopRepCoefficientEquiv A)
    (fun _ _ => rfl) (dehomogenizeTwoOriginal (TopRep.discreteCoefficientTopRep ℤ G A) z)

/-- The discrete comparison commutes with the original cocycle quotient. -/
theorem discreteTopRepH2Equiv_π (A : Rep ℤ G)
    (z : cocycles (TopRep.discreteCoefficientTopRep ℤ G A) 2) :
    discreteTopRepH2Equiv A (π (TopRep.discreteCoefficientTopRep ℤ G A) 2 z) =
      groupCohomology.H2π A (discreteTopRepOriginalTwoCocycle A z) := by
  let X := TopRep.discreteCoefficientTopRep ℤ G A
  let e := discreteTopRepCoefficientEquiv A
  let E := groupCohomology.equivariantH2AddEquiv (MulEquiv.refl G) e (fun _ _ => rfl)
  change E (discreteOriginalH2Equiv X (π X 2 z)) = _
  rw [discreteOriginalH2Equiv_π]
  exact groupCohomology.equivariantH2AddEquiv_H2π (MulEquiv.refl G) e (fun _ _ => rfl)
    (dehomogenizeTwoOriginal X z)

/-- On a discrete coefficient morphism the comparison uses the original group
and coefficient maps. -/
theorem discreteTopRepH2Equiv_map {A : Rep ℤ G} {B : Rep ℤ H}
    (r : H →ₜ* G) (f : Rep.res r.toMonoidHom A ⟶ B)
    (x : continuousCohomology 2 (TopRep.discreteCoefficientTopRep ℤ G A)) :
    discreteTopRepH2Equiv B (ContinuousCohomology.map r (discreteTopRepMap r f) 2 x) =
      groupCohomology.map r.toMonoidHom f 2 (discreteTopRepH2Equiv A x) := by
  obtain ⟨z, rfl⟩ := π_surjective (TopRep.discreteCoefficientTopRep ℤ G A) 2 x
  have hclass := ConcreteCategory.congr_hom (π_map r (discreteTopRepMap r f) 2) z
  change ContinuousCohomology.map r (discreteTopRepMap r f) 2
      (π (TopRep.discreteCoefficientTopRep ℤ G A) 2 z) =
    π (TopRep.discreteCoefficientTopRep ℤ H B) 2
      (cocyclesMap r (discreteTopRepMap r f) 2 z) at hclass
  rw [hclass, discreteTopRepH2Equiv_π, discreteTopRepH2Equiv_π,
    groupCohomology.H2π_comp_map_apply]
  apply congrArg (groupCohomology.H2π B)
  apply groupCohomology.cocycles₂_ext
  intro g h
  change dehomogenizeTwoOriginal (TopRep.discreteCoefficientTopRep ℤ H B)
      (cocyclesMap r (discreteTopRepMap r f) 2 z) (g, h) =
    f (dehomogenizeTwoOriginal (TopRep.discreteCoefficientTopRep ℤ G A) z (r g, r h))
  rw [dehomogenizeTwoOriginal_apply, dehomogenizeTwoOriginal_apply, mappedRelativeCocycle_apply,
    map_one, map_mul]
  rfl

end ContinuousCohomology
