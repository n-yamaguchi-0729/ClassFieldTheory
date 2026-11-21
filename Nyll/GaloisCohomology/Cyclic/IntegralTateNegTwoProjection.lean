/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateCorestrictionNegative
public import Nyll.GaloisCohomology.Cyclic.IntegralTateCupCorestriction
public import Nyll.GaloisCohomology.Cyclic.IntegralTateCyclicCupEvaluation

/-! # Reducing the signed Tate bar evaluation to a cyclic subgroup -/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped RepTensor TensorProduct

namespace IntegralGroupCohomology.Universe

section CommonUniverse

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
  [Fintype H] [Fintype (G ⧸ H)]

/-- When the restriction of a degree-two class is the carry of `b`, its cup
with the same bar representative in the whole group is the negative class
of the actual relative norm of `b`. -/
theorem tateCup_negTwoBar_of_restrict_carry (A B : Rep.{u} ℤ G)
    (g : H) (hg : ∀ h : H, h ∈ Subgroup.zpowers g) (x : A.ρ.invariants)
    (b : (Rep.res H.subtype B).ρ.invariants) (y : tate B 2)
    (hy : tateRestrict H B 2 y = tateCyclicCarryClass (Rep.res H.subtype B) g hg b) :
    tateCup A B (-2) 2 0 (by decide)
      (tateNegTwoBarClass A g.val x.val (x.property g.val⁻¹)) y =
        -fixedClass (A ⊗ᵣ B) (tensorFixedVector A B x (corestrictInvariants H B b)) := by
  let C := Rep.res H.subtype A
  let D := Rep.res H.subtype B
  let x' := restrictInvariants H A x
  let z := tateNegTwoBarClass C g x'.val (x'.property g⁻¹)
  have hz : tateCorestrict H A (-2) z = tateNegTwoBarClass A g.val x.val (x.property g.val⁻¹) :=
    tateCorestrict_negTwoBarClass H A g x.val (x.property g.val⁻¹)
  have hproj := tateCorestrict_cup_restrict_right H A (-2) 2 z B 0 (by decide) y
  have hcyc := tateCup_negTwoBar_carry C D g hg x' b
  have hfixed :
      tateCorestrict H (A ⊗ᵣ B) 0 (fixedClass (C ⊗ᵣ D) (tensorFixedVector C D x' b)) =
        fixedClass (A ⊗ᵣ B) (tensorFixedVector A B x (corestrictInvariants H B b)) := by
    have hfixed' : tensorCupZeroRight C D 0 (fixedClass C x') (fixedClass D b) =
        fixedClass (C ⊗ᵣ D) (tensorFixedVector C D x' b) :=
      tensorCupZeroRight_fixedClasses C D x' b
    rw [← hfixed']
    change tateZeroCorestrict H (A ⊗ᵣ B)
      (tensorCupZeroRight C D 0 (fixedClass C x') (fixedClass D b)) = _
    rw [← tateZeroRestrict_fixedClass, tateZeroCorestrict_cup, tateZeroCorestrict_fixedClass]
    exact tensorCupZeroRight_fixedClasses A B x (corestrictInvariants H B b)
  rw [← hz, ← hproj, hy, hcyc]
  let f := tateCorestrict H (A ⊗ᵣ B) 0
  let z₀ : tate (Rep.res H.subtype (A ⊗ᵣ B)) 0 :=
    fixedClass (C ⊗ᵣ D) (tensorFixedVector C D x' b)
  have h₀ : f z₀ = fixedClass (A ⊗ᵣ B)
      (tensorFixedVector A B x (corestrictInvariants H B b)) := hfixed
  exact (map_neg f z₀).trans (congrArg Neg.neg h₀)

end CommonUniverse

variable {G : Type u} [Group G] [Fintype G]

/-- The subgroup reduction evaluates the original independent-universe cup
on the original trivial-integer bar class and the original norm representative. -/
theorem tateCupTrivialInteger_negTwo_bar_of_restrict_carry (B : Rep.{v} ℤ G)
    (H : Subgroup (ULift.{v} G)) [Fintype H] [Fintype (ULift.{v} G ⧸ H)]
    (g : H) (hg : ∀ h : H, h ∈ Subgroup.zpowers g) (y : tate B 2) (a : B.ρ.invariants)
    (b : (Rep.res H.subtype ((Rep.universeLiftFunctor ℤ G).obj B)).ρ.invariants)
    (hy : let A := (Rep.universeLiftFunctor ℤ G).obj B
      tateRestrict H A 2 ((tateIsoCommon A 2).inv y) =
        tateCyclicCarryClass (Rep.res H.subtype A) g hg b)
    (hn : corestrictInvariants H ((Rep.universeLiftFunctor ℤ G).obj B) b =
      universeLiftFixedVector B a) :
    tateCupTrivialInteger B (-2) 2 0 (by decide) y (tateNegTwoUnitClass G g.val.down) =
      -fixedClass B a := by
  apply tateCupTrivialInteger_negTwo_of_lifted_cup
  intro F I U A i i' a'
  have hgValue : (ULift.up g.val.down : ULift.{v} G) = g.val := ULift.up_down g.val
  rw [hgValue]
  have h := tateCup_negTwoBar_of_restrict_carry H U A g hg i' b
    ((tateIsoCommon A 2).inv y) hy
  exact h.trans (congrArg (fun z => -fixedClass (U ⊗ᵣ A) (tensorFixedVector U A i' z)) hn)

end IntegralGroupCohomology.Universe
