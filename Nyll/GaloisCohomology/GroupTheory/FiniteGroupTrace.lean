/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.H2FiniteIndexTrace
public import Nyll.GaloisCohomology.GroupTheory.InductionCounit
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# The finite group sum of the existing coefficient trace

Tracing a map defined on the trivial subgroup is the actual sum
`∑ g, ρ(g⁻¹) ∘ f ∘ ρ(g)`. The proof evaluates the existing induction-coinduction
comparison and induction counit on their original representatives.
-/

@[expose] public section

noncomputable section

universe r u v

open CategoryTheory
open scoped BigOperators

namespace ClassFieldTower.Cohomology

variable {R : Type r} {G : Type u} [CommRing R] [Group G] [Fintype G]

/-- The actual finite-index trace for the trivial subgroup evaluates as the
sum of conjugates of the original restricted coefficient morphism. -/
theorem finiteIndexHomTrace_bot_apply (A B : Rep.{max r u v} R G)
    (f : Rep.res (⊥ : Subgroup G).subtype A ⟶ Rep.res (⊥ : Subgroup G).subtype B)
    (a : A) :
    (finiteIndexHomTrace.{r, u, v} B (⊥ : Subgroup G) A f).hom a =
      ∑ g : G, B.ρ g⁻¹ (f.hom (A.ρ g a)) := by
  classical
  let : Fintype (G ⧸ (⊥ : Subgroup G)) := Subgroup.fintypeQuotientOfFiniteIndex
  let T := Rep.res (⊥ : Subgroup G).subtype B
  let : Module R T.V := T.hV2
  change ((Rep.indResHomEquiv.{max r u v} (⊥ : Subgroup G).subtype T B).symm (𝟙 _)).hom
      (Rep.coindToInd T
        ((Rep.resCoindHomEquiv.{max r u v} (⊥ : Subgroup G).subtype A T f).hom a)) = _
  rw [Rep.coindToInd_apply, map_sum]
  have hbij : Function.Bijective
      (fun g : G => (⟦g⟧ : Quotient (QuotientGroup.rightRel (⊥ : Subgroup G)))) := by
    constructor
    · intro g h he
      obtain ⟨s, hs⟩ := Quotient.exact he
      have hs1 : s = 1 := Subsingleton.elim _ _
      subst s
      simpa only [one_smul] using hs.symm
    · intro q
      induction q using Quotient.inductionOn with
      | h g => exact ⟨g, rfl⟩
  symm
  refine Fintype.sum_bijective
    (fun g : G => (⟦g⟧ : Quotient (QuotientGroup.rightRel (⊥ : Subgroup G))))
    hbij _ _ ?_
  intro g
  change B.ρ g⁻¹ (f.hom (A.ρ g a)) =
    ((Rep.indResHomEquiv.{max r u v} (⊥ : Subgroup G).subtype T B).symm (𝟙 _)).hom
      (Representation.IndV.mk (⊥ : Subgroup G).subtype T.ρ g (f.hom (A.ρ g a)))
  exact (Rep.indResHomEquiv_symm_apply_mk (⊥ : Subgroup G).subtype T B (𝟙 _)
    g (f.hom (A.ρ g a))).symm

end ClassFieldTower.Cohomology
