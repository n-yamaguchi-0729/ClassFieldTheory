/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousCochainTuples
public import Nyll.GaloisCohomology.Topology.HomogeneousContinuousCochainsFunctor
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Lifting homogeneous continuous cochains

A surjective map with discrete target coefficients lifts homogeneous cochains
when the source action is jointly continuous. Normalizing the first coordinate
makes an arbitrary section equivariant without averaging.
-/

@[expose] public section

noncomputable section

universe u
open CategoryTheory

namespace TopRep

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A B : TopRep.{u} ℤ G)

/-- A jointly continuous coefficient action gives equivariant continuous lifts
of homogeneous tuples whenever its values admit lifts along the equivariant coefficient map. -/
theorem exists_equivariant_continuous_tuple_lift [DiscreteTopology B]
    (φ : A ⟶ B)
    (hA : Continuous (fun p : G × A => A.ρ p.1 p.2))
    (n : ℕ) (f : C(Fin (n + 1) → G, B))
    (hf : ∀ σ a, f (fun i => σ * a i) = B.ρ σ (f a))
    (hlift : ∀ a, ∃ x : A, φ x = f a) :
    ∃ g : C(Fin (n + 1) → G, A),
      (∀ σ a, g (fun i => σ * a i) = A.ρ σ (g a)) ∧
      ∀ a, φ (g a) = f a := by
  classical
  let s : B → A := fun b => if h : ∃ x : A, φ x = b then h.choose else 0
  have hs (a : Fin (n + 1) → G) : φ (s (f a)) = f a := by
    change φ (if h : ∃ x : A, φ x = f a then h.choose else 0) = f a
    rw [dite_eq_left (hlift a)]
    exact (hlift a).choose_spec
  let norm : (Fin (n + 1) → G) → (Fin (n + 1) → G) :=
    fun a i => (a 0)⁻¹ * a i
  have hn : Continuous norm :=
    continuous_pi (fun i => (continuous_apply 0).inv.mul (continuous_apply i))
  let g : C(Fin (n + 1) → G, A) :=
    ⟨fun a => A.ρ (a 0) (s (f (norm a))),
      hA.comp ((continuous_apply 0).prodMk
        ((show Continuous s from continuous_of_discreteTopology).comp
          (f.continuous.comp hn)))⟩
  refine ⟨g, ?_, ?_⟩
  · intro σ a
    have hnorm : norm (fun i => σ * a i) = norm a := by
      funext i
      change (σ * a 0)⁻¹ * (σ * a i) = (a 0)⁻¹ * a i
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    change A.ρ (σ * a 0) (s (f (norm (fun i => σ * a i))) ) =
      A.ρ σ (A.ρ (a 0) (s (f (norm a))))
    rw [hnorm]
    exact congrArg (fun t => t (s (f (norm a)))) (map_mul A.ρ σ (a 0))
  · intro a
    change φ.hom (A.ρ (a 0) (s (f (norm a)))) = f a
    rw [hom_comm_apply, hs]
    have hnorm : (fun i => a 0 * norm a i) = a := by
      funext i
      exact mul_inv_cancel_left (a 0) (a i)
    exact (hf (a 0) (norm a)).symm.trans (congrArg f hnorm)

/-- Tuple evaluation intertwines the actual resolution map with application
of the coefficient morphism. -/
theorem resolutionTupleHomeomorph_resolutionMap [LocallyCompactSpace G]
    (φ : A ⟶ B) (n : ℕ) (f : resolutionX A n) (a : Fin n → G) :
    resolutionTupleHomeomorph G B n
      ((ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) φ n).hom f) a =
      φ (resolutionTupleHomeomorph G A n f a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact ih (f (a 0)) (fun i => a i.succ)

/-- A homogeneous cochain lifts whenever all of its tuple values lift.
This shares the normalized equivariant lifting step without requiring
global surjectivity of the coefficient map. -/
theorem homogeneousCochains_map_preimage_of_tuple_preimages [LocallyCompactSpace G]
    [DiscreteTopology B] (φ : A ⟶ B)
    (hA : Continuous (fun p : G × A => A.ρ p.1 p.2)) (n : ℕ)
    (z : (homogeneousCochains B).X n)
    (h : ∀ a : Fin (n + 1) → G, ∃ x : A,
      φ x = resolutionTupleHomeomorph G B (n + 1) z.val a) :
    ∃ b : (homogeneousCochains A).X n,
      (ContinuousCohomology.cochainsMap
        (ContinuousMonoidHom.id G) φ).f n b = z := by
  let f := resolutionTupleHomeomorph G B (n + 1) z.val
  have hf := homogeneousCochain_tuple_equivariant G B n z
  obtain ⟨g, hg, hfg⟩ :=
    exists_equivariant_continuous_tuple_lift G A B φ hA n f hf h
  refine ⟨homogeneousCochainOfTuple G A n g hg, ?_⟩
  apply Subtype.ext
  apply (resolutionTupleHomeomorph G B (n + 1)).injective
  apply ContinuousMap.ext
  intro a
  change resolutionTupleHomeomorph G B (n + 1)
    ((ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) φ (n + 1)).hom
      (homogeneousCochainOfTuple G A n g hg).val) a = f a
  rw [resolutionTupleHomeomorph_resolutionMap]
  exact (congrArg (fun t : C(Fin (n + 1) → G, A) => φ (t a))
    (homogeneousCochainOfTuple_apply G A n g hg)).trans (hfg a)

/-- Surjective discrete coefficient maps are surjective on actual homogeneous
continuous cochains when the source action is jointly continuous. -/
theorem homogeneousCochains_map_surjective [LocallyCompactSpace G]
    [DiscreteTopology B] (φ : A ⟶ B) (hφ : Function.Surjective φ)
    (hA : Continuous (fun p : G × A => A.ρ p.1 p.2)) (n : ℕ) :
    Function.Surjective
      ((ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) φ).f n) := by
  intro z
  exact homogeneousCochains_map_preimage_of_tuple_preimages G A B φ hA n z
    (fun a => hφ (resolutionTupleHomeomorph G B (n + 1) z.val a))

/-- Injective coefficient maps are injective on actual homogeneous continuous
cochains. -/
theorem homogeneousCochains_map_injective [LocallyCompactSpace G]
    (φ : A ⟶ B) (hφ : Function.Injective φ) (n : ℕ) :
    Function.Injective
      ((ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) φ).f n) := by
  intro x y h
  apply Subtype.ext
  apply (resolutionTupleHomeomorph G A (n + 1)).injective
  apply ContinuousMap.ext
  intro a
  apply hφ
  have hh := congrArg
    (fun z : (homogeneousCochains B).X n =>
      resolutionTupleHomeomorph G B (n + 1) z.val a) h
  exact (resolutionTupleHomeomorph_resolutionMap G A B φ (n + 1) x.val a).symm.trans
    (hh.trans (resolutionTupleHomeomorph_resolutionMap G A B φ (n + 1) y.val a))

/-- Actual homogeneous continuous cochain maps are additive in the coefficient
morphism. -/
theorem homogeneousCochains_map_add [LocallyCompactSpace G]
    (φ ψ : A ⟶ B) :
    ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) (φ + ψ) =
      ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) φ +
        ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) ψ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  apply (resolutionTupleHomeomorph G B (n + 1)).injective
  apply ContinuousMap.ext
  intro a
  change resolutionTupleHomeomorph G B (n + 1)
      ((ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G)
        (φ + ψ) (n + 1)).hom z.val) a =
    resolutionTupleHomeomorph G B (n + 1)
      (((ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) φ (n + 1)).hom z.val) +
        ((ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) ψ (n + 1)).hom z.val)) a
  have htotal := resolutionTupleHomeomorph_resolutionMap G A B (φ + ψ) (n + 1) z.val a
  have hφ := resolutionTupleHomeomorph_resolutionMap G A B φ (n + 1) z.val a
  have hψ := resolutionTupleHomeomorph_resolutionMap G A B ψ (n + 1) z.val a
  have hsum := congrArg (fun t : C(Fin (n + 1) → G, B) => t a)
    (resolutionTupleHomeomorph_add G B (n + 1)
      ((ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) φ (n + 1)).hom z.val)
      ((ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) ψ (n + 1)).hom z.val))
  have hcoeff :
      (φ + ψ) (resolutionTupleHomeomorph G A (n + 1) z.val a) =
      φ (resolutionTupleHomeomorph G A (n + 1) z.val a) +
        ψ (resolutionTupleHomeomorph G A (n + 1) z.val a) := rfl
  exact htotal.trans (hcoeff.trans
    ((congrArg₂ (fun x y : B => x + y) hφ hψ).symm.trans hsum.symm))

/-- Exactness of discrete coefficient maps lifts to actual homogeneous
continuous cochains, using normalized equivariant lifts. -/
theorem homogeneousCochains_map_exact [LocallyCompactSpace G]
    [DiscreteTopology B] (C : TopRep.{u} ℤ G)
    (φ : A ⟶ B) (ψ : B ⟶ C)
    (h : ∀ y : B, ψ y = 0 → ∃ x : A, φ x = y)
    (hA : Continuous (fun p : G × A => A.ρ p.1 p.2))
    (n : ℕ) (z : (homogeneousCochains B).X n)
    (hz : (ContinuousCohomology.cochainsMap
      (ContinuousMonoidHom.id G) ψ).f n z = 0) :
    ∃ b : (homogeneousCochains A).X n,
      (ContinuousCohomology.cochainsMap
        (ContinuousMonoidHom.id G) φ).f n b = z := by
  let f := resolutionTupleHomeomorph G B (n + 1) z.val
  have hzero (a : Fin (n + 1) → G) : ψ (f a) = 0 := by
    have hh := congrArg
      (fun w : (homogeneousCochains C).X n =>
        resolutionTupleHomeomorph G C (n + 1) w.val a) hz
    have h0 : resolutionTupleHomeomorph G C (n + 1) 0 a = 0 :=
      congrArg (fun t : C(Fin (n + 1) → G, C) => t a)
        (resolutionTupleContinuousLinearEquiv G C (n + 1)).map_zero
    exact (resolutionTupleHomeomorph_resolutionMap G B C ψ (n + 1) z.val a).symm.trans
      (hh.trans h0)
  exact homogeneousCochains_map_preimage_of_tuple_preimages G A B φ hA n z
    (fun a => h (f a) (hzero a))

/-- Actual homogeneous continuous cochains as a functor of the coefficient
topological representation. -/
def homogeneousContinuousCochainsFunctor :
    TopRep.{u} ℤ G ⥤ CochainComplex (TopModuleCat.{u} ℤ) ℕ :=
  homogeneousContinuousCochainsFunctorOver ℤ G

/-- The actual homogeneous continuous cochain functor is additive. -/
instance homogeneousContinuousCochainsFunctor_additive [LocallyCompactSpace G] :
    (homogeneousContinuousCochainsFunctor G).Additive where
  map_add := by
    intro A B φ ψ
    exact homogeneousCochains_map_add G A B φ ψ

end TopRep
