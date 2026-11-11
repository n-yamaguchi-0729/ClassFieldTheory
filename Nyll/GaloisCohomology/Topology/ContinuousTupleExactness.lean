/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.ContinuousCochainTuples
public import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives

/-!
# Passing explicit tuple primitives to actual continuous cohomology

These lemmas share the tuple-to-homology step between geometric-section
primitives and explicit coinduced contractions.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory

namespace TopRep

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] (X : TopRep.{u} ℤ G)

/-- Explicit equivariant tuple primitives produce actual homogeneous boundaries. -/
theorem exists_homogeneousCochain_primitive_of_tuple_primitives (n : ℕ)
    (hprimitive : ∀ (f : C(Fin (n + 2) → G, X)),
      (∀ (σ : G) (a : Fin (n + 2) → G), f (fun i => σ * a i) = X.ρ σ (f a)) →
      (∀ a : Fin (n + 3) → G, ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
        f (fun j => a (i.succAbove j)) = 0) →
      ∃ g : C(Fin (n + 1) → G, X),
        (∀ (σ : G) (a : Fin (n + 1) → G), g (fun i => σ * a i) = X.ρ σ (g a)) ∧
        ∀ a : Fin (n + 2) → G, ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          g (fun j => a (i.succAbove j)) = f a)
    (z : (homogeneousCochains X).X (n + 1))
    (hz : (homogeneousCochains X).d (n + 1) (n + 2) z = 0) :
    ∃ b : (homogeneousCochains X).X n,
      (homogeneousCochains X).d n (n + 1) b = z := by
  let f : C(Fin (n + 2) → G, X) :=
    resolutionTupleHomeomorph G X (n + 2) z.val
  have heq (σ : G) (a : Fin (n + 2) → G) :
      f (fun i => σ * a i) = X.ρ σ (f a) :=
    homogeneousCochain_tuple_equivariant G X (n + 1) z σ a
  have hd0 : (d X (n + 2)).hom z.val = 0 :=
    (homogeneousCochains.d_apply X (n + 1) z).symm.trans
      (congrArg Subtype.val hz)
  have hc (a : Fin (n + 3) → G) :
      ∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) • f (fun j => a (i.succAbove j)) = 0 := by
    have h0 : resolutionTupleHomeomorph G X (n + 3) 0 a = 0 :=
      congrArg (fun h : C(Fin (n + 3) → G, X) => h a)
        (resolutionTupleContinuousLinearEquiv G X (n + 3)).map_zero
    exact (resolutionTupleHomeomorph_d G X (n + 2) z.val a).symm.trans
      ((congrArg (fun x => resolutionTupleHomeomorph G X (n + 3) x a) hd0).trans h0)
  obtain ⟨g, hg, hdg⟩ := hprimitive f heq hc
  let b := homogeneousCochainOfTuple G X n g hg
  refine ⟨b, ?_⟩
  apply Subtype.ext
  apply (resolutionTupleHomeomorph G X (n + 2)).injective
  apply ContinuousMap.ext
  intro a
  have h₁ := congrArg
    (fun x => resolutionTupleHomeomorph G X (n + 2) x a)
    (homogeneousCochains.d_apply X n b)
  have h₂ := resolutionTupleHomeomorph_d G X (n + 1) b.val a
  have h₃ :
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        resolutionTupleHomeomorph G X (n + 1) b.val
          (fun j => a (i.succAbove j))) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • g (fun j => a (i.succAbove j)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun x => ((-1 : ℤ) ^ (i : ℕ)) • x)
      (congrArg (fun h : C(Fin (n + 1) → G, X) => h (fun j => a (i.succAbove j)))
        (homogeneousCochainOfTuple_apply G X n g hg))
  exact h₁.trans (h₂.trans (h₃.trans (hdg a)))

omit [LocallyCompactSpace G] in
/-- Actual cochain primitives kill the corresponding actual cohomology group. -/
theorem continuousCohomology_eq_zero_of_cochain_primitives (n : ℕ)
    (hprimitive : ∀ (z : (homogeneousCochains X).X (n + 1)),
      (homogeneousCochains X).d (n + 1) (n + 2) z = 0 →
      ∃ b : (homogeneousCochains X).X n,
        (homogeneousCochains X).d n (n + 1) b = z)
    (a : continuousCohomology (n + 1) X) : a = 0 := by
  let C := homogeneousCochains X
  obtain ⟨z, rfl⟩ := ContinuousCohomology.π_surjective X (n + 1) a
  let z₀ := C.iCycles (n + 1) z
  have hz₀ : C.d (n + 1) (n + 2) z₀ = 0 :=
    ConcreteCategory.congr_hom (C.iCycles_d (n + 1) (n + 2)) z
  obtain ⟨b, hb⟩ := hprimitive z₀ hz₀
  have hi : Function.Injective (C.iCycles (n + 1)) :=
    (ModuleCat.mono_iff_injective
      ((forget₂ (TopModuleCat ℤ) (ModuleCat ℤ)).map (C.iCycles (n + 1)))).mp inferInstance
  have hbc : C.toCycles n (n + 1) b = z := by
    apply hi
    exact (ConcreteCategory.congr_hom (C.toCycles_i n (n + 1)) b).trans hb
  change C.homologyπ (n + 1) z = 0
  rw [← hbc]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ n (n + 1)) b

end TopRep
