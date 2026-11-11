/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.FinitePGroupInvariants
public import Nyll.GaloisCohomology.Topology.InvariantCoefficientExactness
public import Nyll.GaloisCohomology.Topology.TrivialIntegralCoefficientLine
public import Nyll.GaloisCohomology.Topology.TrivialDegreeTwoCocycles
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.LinearAlgebra.Quotient.Card
public import Nyll.GaloisCohomology.ProP.TrivialZModP

/-!
# Finite coefficients with p-group action image

Vanishing in degree two for the actual trivial mod-p coefficient object
extends to every finite module killed by p whose action image is a p-group.
The proof uses an actual invariant line, its actual coefficient quotient,
and the long exact sequence. No p-group assumption is made on the abstract
acting group.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits ContRepresentation

namespace TopRep

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] (p : ℕ) [Fact p.Prime]

/-- Degree-two vanishing for trivial mod-p coefficients extends to actual
finite p-torsion coefficients with p-group action image. -/
theorem continuousModuleH2_isZero_of_pGroup_image
    (htriv : IsZero (((continuousModuleComplexFunctor G).obj
      (ClassFieldTower.Cohomology.trivialIntegralZModPLifted p G)).homology 2))
    (X : TopRep.{u} ℤ G) [Finite X] [DiscreteTopology X]
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2))
    (hp : ∀ x : X, p • x = 0)
    (hρ : let _ : Module ℤ X := X.hV2;
      IsPGroup p X.ρ.toRepresentation.asGroupHom.range) :
    IsZero (((continuousModuleComplexFunctor G).obj X).homology 2) := by
  classical
  suffices step : ∀ n : ℕ, ∀ (Y : TopRep.{u} ℤ G) [Finite Y] [DiscreteTopology Y],
      Nat.card Y = n →
      Continuous (fun gy : G × Y => Y.ρ gy.1 gy.2) →
      (∀ y : Y, p • y = 0) →
      (let _ : Module ℤ Y := Y.hV2;
        IsPGroup p Y.ρ.toRepresentation.asGroupHom.range) →
      IsZero (((continuousModuleComplexFunctor G).obj Y).homology 2) by
    exact step (Nat.card X) X rfl hX hp hρ
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Y hfin hdisc hcard hY hpY hρY
    cases subsingleton_or_nontrivial Y with
    | inl hsub =>
      have : Subsingleton Y := hsub
      apply continuousModuleComplex_isZero_of_cohomology_eq_zero G Y 2
      exact TrivialDegreeTwoCocycles.continuousH2_eq_zero_of_primitive Y
        (fun _ _ => Subsingleton.elim _ _)
        (fun _ _ => ⟨0, fun _ _ => Subsingleton.elim _ _⟩)
    | inr hnontriv =>
      have : Nontrivial Y := hnontriv
      let : Module ℤ Y := Y.hV2
      obtain ⟨v, hv, hfix⟩ :=
        Representation.exists_nonzero_fixed_of_image_isPGroup_int
          Y.ρ.toRepresentation hρY hpY
      let T := ClassFieldTower.Cohomology.trivialIntegralZModPLifted p G
      let φ : T ⟶ Y := trivialIntegralCoefficientLineHom G Y p v (hpY v) hfix
      have hφ : Function.Injective φ :=
        trivialIntegralCoefficientLineHom_injective G Y p v (hpY v) hfix hv
      let W := LinearMap.range φ.hom.toContinuousLinearMap.toLinearMap
      have hW : ∀ g : G, W ≤ W.comap (Y.ρ g).toLinearMap := by
        rintro g y ⟨t, rfl⟩
        exact ⟨T.ρ g t, φ.hom.isIntertwining g t⟩
      let Q := invariantCoefficientQuotient ℤ G Y W hW
      let q : Y ⟶ Q := invariantCoefficientQuotientProjection ℤ G Y W hW
      have : Finite (Y ⧸ W) := Finite.of_surjective W.mkQ W.mkQ_surjective
      have : Finite Q := inferInstanceAs (Finite (Y ⧸ W))
      have : DiscreteTopology Q := invariantCoefficientQuotient_discrete ℤ G Y W hW
      have hQcont : Continuous (fun gq : G × Q => Q.ρ gq.1 gq.2) :=
        invariantCoefficientQuotient_action_continuous ℤ G Y W hW hY
      have hpQ : ∀ z : Q, p • z = 0 := by
        intro z
        obtain ⟨y, rfl⟩ := invariantCoefficientQuotientProjection_surjective ℤ G Y W hW z
        have heq := congrArg (fun y : Y => q.hom y) (hpY y)
        simpa only [map_nsmul, map_zero] using heq
      let : Module ℤ Q := Q.hV2
      have hρQ : IsPGroup p Q.ρ.toRepresentation.asGroupHom.range :=
        Representation.isPGroup_quotient_image Y.ρ.toRepresentation W hW hρY
      have : Nontrivial W := by
        apply nontrivial_of_ne (⟨φ (ULift.up (1 : ZMod p)), ⟨_, rfl⟩⟩ : W) 0
        intro heq
        have hz : φ (ULift.up (1 : ZMod p)) = φ 0 :=
          (congrArg Subtype.val heq).trans (map_zero φ.hom).symm
        exact one_ne_zero (congrArg ULift.down (hφ hz))
      have : Fintype W := Fintype.ofFinite W
      have hWcard : 1 < Nat.card W := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.one_lt_card
      have hlt : Nat.card Q < Nat.card Y := by
        change Nat.card (Y ⧸ W) < Nat.card Y
        rw [W.card_eq_card_quotient_mul_card]
        simpa only [one_mul] using
          Nat.mul_lt_mul_of_pos_right
            hWcard
            (Nat.card_pos : 0 < Nat.card (Y ⧸ W))
      have hQ := ih (Nat.card Q) (hcard ▸ hlt) Q rfl hQcont hpQ hρQ
      have hTcont : Continuous (fun gt : G × T => T.ρ gt.1 gt.2) := continuous_snd
      have hS := coefficientRangeContinuousModule_shortExact G T Y φ hφ hTcont hY
      exact (hS.homology_exact₂ 2).isZero_X₂
        (htriv.eq_of_src _ _) (hQ.eq_of_tgt _ _)

end TopRep
