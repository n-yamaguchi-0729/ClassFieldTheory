/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.IntegralTateCoinduction
public import Nyll.GaloisCohomology.Cyclic.IntegralTateSplitSequences
public import Nyll.GaloisCohomology.GroupTheory.FiniteGroupTrace
public import Nyll.GaloisCohomology.GroupTheory.H2FiniteIndexTrace
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.GroupTheory.Index

/-!
# Coefficient traces vanish on integral Tate cohomology

The existing finite-index coefficient trace factors through actual coinduction.
For the trivial subgroup its middle Tate object vanishes in every integer
degree. In particular the group order annihilates every original integral
Tate group, including independently sized coefficient modules.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open scoped BigOperators

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G] [Fintype G]

/-- The original integral Tate functor inherits additivity from the native Tate complex. -/
instance tateFunctor_additive (n : ℤ) : (tateFunctor.{u, v} G n).Additive := by
  dsimp only [tateFunctor, tateCohomologyFunctor]
  infer_instance

/-- Tracing a morphism defined on the trivial subgroup induces zero in every
Tate degree: its actual coefficient trace factors through a Tate acyclic object. -/
theorem tate_map_trivialSubgroupTrace_eq_zero {A B : Rep.{u} ℤ G}
    (f : Rep.res (⊥ : Subgroup G).subtype A ⟶ Rep.res (⊥ : Subgroup G).subtype B)
    (n : ℤ) :
    (tateFunctor G n).map
      (ClassFieldTower.Cohomology.finiteIndexHomTrace.{0, u, 0} B (⊥ : Subgroup G) A f) =
        0 := by
  let H : Subgroup G := ⊥
  let C := Rep.coind H.subtype (Rep.res H.subtype B)
  let a : A ⟶ C := Rep.resCoindHomEquiv.{u} H.subtype A (Rep.res H.subtype B) f
  let b : C ⟶ B := ClassFieldTower.Cohomology.finiteIndexCoefficientTrace.{0, u, 0} B H
  have hzero : Limits.IsZero (tate C n) := coind_tate_isZero (Rep.res H.subtype B) n
  have hb : (tateFunctor G n).map b = 0 := hzero.eq_of_src ((tateFunctor G n).map b) 0
  change (tateFunctor G n).map (a ≫ b) = 0
  rw [CategoryTheory.Functor.map_comp, hb, CategoryTheory.Limits.comp_zero]

/-- If the identity is the original sum of conjugates of a linear map, then
the coefficient representation is Tate acyclic in every degree. -/
theorem tate_isZero_of_trace_identity (A : Rep.{u} ℤ G) (p : A →ₗ[ℤ] A)
    (hp : ∀ a : A, a = ∑ g : G, A.ρ g⁻¹ (p (A.ρ g a))) (n : ℤ) :
    Limits.IsZero (tate A n) := by
  let f := restrictBotLinearHom (A := A) (B := A) p
  have htrace : ClassFieldTower.Cohomology.finiteIndexHomTrace.{0, u, 0}
      A (⊥ : Subgroup G) A f = 𝟙 A := by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro a
    rw [ClassFieldTower.Cohomology.finiteIndexHomTrace_bot_apply]
    exact (hp a).symm
  have hzero := tate_map_trivialSubgroupTrace_eq_zero f n
  rw [htrace, (tateFunctor G n).map_id A] at hzero
  exact (Limits.IsZero.iff_id_eq_zero _).mpr hzero

/-- The group-order multiple of any original coefficient morphism induces zero. -/
theorem tate_map_card_nsmul_eq_zero {A B : Rep.{u} ℤ G} (f : A ⟶ B) (n : ℤ) :
    (tateFunctor G n).map (Nat.card G • f) = 0 := by
  have h := tate_map_trivialSubgroupTrace_eq_zero
    ((Rep.resFunctor (⊥ : Subgroup G).subtype).map f) n
  rw [ClassFieldTower.Cohomology.finiteIndexHomTrace_restriction, Subgroup.index_bot] at h
  exact h

/-- The group order annihilates every actual Tate class in a common working universe. -/
theorem card_nsmul_tate_eq_zero_common (A : Rep.{u} ℤ G) (n : ℤ) (x : tate A n) :
    Nat.card G • x = 0 := by
  have h := tate_map_card_nsmul_eq_zero (𝟙 A) n
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] at h
  exact congrArg (fun f : tate A n ⟶ tate A n => f.hom x) h

/-- The group order annihilates the existing Tate object for independently sized
groups and coefficients; the comparison is the established native-complex map. -/
theorem card_nsmul_tate_eq_zero (A : Rep.{v} ℤ G) (n : ℤ) (x : tate A n) :
    Nat.card G • x = 0 := by
  let B := (Rep.universeLiftFunctor ℤ G).obj A
  let e := tateIsoCommon B n
  have h := congrArg (fun y => e.hom y)
    (card_nsmul_tate_eq_zero_common B n (e.inv x))
  rw [map_nsmul, map_zero] at h
  have he : e.hom (e.inv x) = x := e.toLinearEquiv.apply_symm_apply x
  rw [he] at h
  have hcard : Nat.card (ULift.{v} G) = Nat.card G :=
    Nat.card_congr (Equiv.ulift : ULift.{v} G ≃ G)
  rwa [hcard] at h

end IntegralGroupCohomology.Universe
