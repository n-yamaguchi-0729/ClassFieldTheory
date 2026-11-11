/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.FiniteInvariantCoefficients
public import Nyll.GaloisCohomology.Topology.InvariantCoefficientSubrepresentation
public import Nyll.GaloisCohomology.Topology.ContinuousEquivariantTupleLifting
public import Nyll.GaloisCohomology.Topology.ContinuousModuleExactness

/-!
# Finite coefficient realizations of actual continuous cochains

A bounded-torsion discrete continuous cochain on a compact group factors
through an actual finite invariant coefficient subrepresentation. Its
closedness is reflected by the injective coefficient inclusion.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory ContRepresentation

namespace TopRep

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (X : TopRep.{u} ℤ G) [DiscreteTopology X]

/-- Every actual bounded-torsion continuous homogeneous cochain is the
image of a cochain in finite invariant coefficients. -/
theorem exists_finite_coefficient_cochain_preimage
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (m : ℤ) (hm0 : m ≠ 0) (hm : ∀ x : X, m • x = 0)
    (n : ℕ) (z : (homogeneousCochains X).X n) :
    ∃ (Y : TopRep.{u} ℤ G) (φ : Y ⟶ X),
      Finite Y ∧ DiscreteTopology Y ∧
      Continuous (fun gy : G × Y => Y.ρ gy.1 gy.2) ∧
      (∀ y : Y, m • y = 0) ∧ Function.Injective φ ∧
      ∃ b : (homogeneousCochains Y).X n,
        (ContinuousCohomology.cochainsMap
          (ContinuousMonoidHom.id G) φ).f n b = z := by
  let f := resolutionTupleHomeomorph G X (n + 1) z.val
  have hf : (Set.range f).Finite :=
    (isCompact_range f.continuous).finite
      (isDiscrete_iff_discreteTopology.mpr inferInstance)
  obtain ⟨W, hfW, hfin, hW⟩ :=
    exists_finite_invariant_submodule_of_annihilator ℤ G X hX m hm0 hm
      (Set.range f) hf
  let Y := invariantSubmoduleTopRep ℤ G X W hW
  let φ : Y ⟶ X := invariantSubmoduleInclusion ℤ G X W hW
  have : Finite Y := hfin
  have : DiscreteTopology Y := invariantSubmoduleTopRep_discrete ℤ G X W hW
  have hY : Continuous (fun gy : G × Y => Y.ρ gy.1 gy.2) :=
    invariantSubmoduleTopRep_action_continuous ℤ G X W hW hX
  have hmY : ∀ y : Y, m • y = 0 := by
    intro y
    apply Subtype.ext
    exact hm ((show W from y).val)
  obtain ⟨b, hb⟩ := homogeneousCochains_map_preimage_of_tuple_preimages
    G Y X φ hY n z (fun a => ⟨⟨f a, hfW ⟨a, rfl⟩⟩, rfl⟩)
  exact ⟨Y, φ, inferInstance, inferInstance, hY, hmY,
    invariantSubmoduleInclusion_injective ℤ G X W hW, b, hb⟩

/-- Closed actual cochains lift to closed cochains in finite coefficients,
because the inclusion is injective in every cochain degree. -/
theorem exists_finite_coefficient_closed_cochain_preimage
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (m : ℤ) (hm0 : m ≠ 0) (hm : ∀ x : X, m • x = 0)
    (n : ℕ) (z : (homogeneousCochains X).X n)
    (hz : (homogeneousCochains X).d n (n + 1) z = 0) :
    ∃ (Y : TopRep.{u} ℤ G) (φ : Y ⟶ X),
      Finite Y ∧ DiscreteTopology Y ∧
      Continuous (fun gy : G × Y => Y.ρ gy.1 gy.2) ∧
      (∀ y : Y, m • y = 0) ∧ Function.Injective φ ∧
      ∃ b : (homogeneousCochains Y).X n,
        (ContinuousCohomology.cochainsMap
          (ContinuousMonoidHom.id G) φ).f n b = z ∧
        (homogeneousCochains Y).d n (n + 1) b = 0 := by
  obtain ⟨Y, φ, hfin, hdisc, hY, hmY, hinj, b, hb⟩ :=
    exists_finite_coefficient_cochain_preimage G X hX m hm0 hm n z
  refine ⟨Y, φ, hfin, hdisc, hY, hmY, hinj, b, hb, ?_⟩
  have reflect_closed {C D : CochainComplex (TopModuleCat.{u} ℤ) ℕ}
      (ψ : C ⟶ D) (i j : ℕ) (hinj : Function.Injective (ψ.f j))
      (b : C.X i) (z : D.X i) (hb : ψ.f i b = z) (hz : D.d i j z = 0) :
      C.d i j b = 0 := by
    apply hinj
    have hcomm := ConcreteCategory.congr_hom (ψ.comm i j) b
    exact hcomm.symm.trans
      ((congrArg (fun t : D.X i => D.d i j t) hb).trans
        (hz.trans (map_zero (ψ.f j).hom).symm))
  exact reflect_closed
    (ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) φ)
    n (n + 1) (homogeneousCochains_map_injective G Y X φ hinj (n + 1))
    b z hb hz

/-- Vanishing for actual finite bounded-torsion coefficient representations
implies vanishing for all discrete representations with the same bound. -/
theorem continuousModule_isZero_of_finite_coefficients
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (m : ℤ) (hm0 : m ≠ 0) (hm : ∀ x : X, m • x = 0)
    (n : ℕ)
    (hfinite : ∀ (Y : TopRep.{u} ℤ G) [Finite Y] [DiscreteTopology Y],
      Continuous (fun gy : G × Y => Y.ρ gy.1 gy.2) →
      (∀ y : Y, m • y = 0) →
      Limits.IsZero (((continuousModuleComplexFunctor G).obj Y).homology (n + 1))) :
    Limits.IsZero (((continuousModuleComplexFunctor G).obj X).homology (n + 1)) := by
  let C := (continuousModuleComplexFunctor G).obj X
  apply (C.exactAt_iff_isZero_homology (n + 1)).mp
  apply (C.exactAt_iff' n (n + 1) (n + 2)
    (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))).mpr
  apply (C.sc' n (n + 1) (n + 2)).exact_iff_of_hasForget.mpr
  intro z hz
  obtain ⟨Y, φ, hfin, hdisc, hY, hmY, _hinj, b, hb, hbzero⟩ :=
    exists_finite_coefficient_closed_cochain_preimage G X hX m hm0 hm
      (n + 1) z hz
  have : Finite Y := hfin
  have : DiscreteTopology Y := hdisc
  let D := (continuousModuleComplexFunctor G).obj Y
  have hD : D.ExactAt (n + 1) :=
    (D.exactAt_iff_isZero_homology (n + 1)).mpr (hfinite Y hY hmY)
  have hD' : (D.sc' n (n + 1) (n + 2)).Exact :=
    (D.exactAt_iff' n (n + 1) (n + 2)
      (CochainComplex.prev_nat_succ n) (CochainComplex.next ℕ (n + 1))).mp hD
  obtain ⟨c, hc⟩ := (D.sc' n (n + 1) (n + 2)).exact_iff_of_hasForget.mp hD' b hbzero
  let ψ := ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) φ
  refine ⟨ψ.f n c, ?_⟩
  have hcomm :
      (homogeneousCochains X).d n (n + 1) (ψ.f n c) =
        ψ.f (n + 1) ((homogeneousCochains Y).d n (n + 1) c) :=
    ConcreteCategory.congr_hom (ψ.comm n (n + 1)) c
  exact hcomm.trans ((congrArg (fun y : (homogeneousCochains Y).X (n + 1) =>
    ψ.f (n + 1) y) hc).trans hb)

end TopRep
