/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# The original relative Frobenius on geometric points

The base-changed Frobenius used on cohomology acts on original geometric
points by the arithmetic Frobenius on their values. The comparison uses
the actual scheme endomorphism and all its native categorical powers.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]

local notation "b" => Spec.algebraMap k Ω
local notation "f" => (X ↘ Spec (CommRingCat.of k))
local notation "Y" => pullback f b
local notation "F" => constantBaseChangeFrobenius k Ω X
local notation "σ" => FiniteField.frobeniusAlgEquivOfAlgebraic k Ω

private local instance constantSpecOver :
    (Spec (CommRingCat.of Ω)).Over (Spec (CommRingCat.of k)) := ⟨b⟩

/-- Projecting the actual Frobenius image of a geometric point is the
arithmetic Frobenius acting on that original point's values. -/
theorem constantBaseChangeFrobenius_point_fst (x : Spec (.of Ω) ⟶ Y) :
    (x ≫ F) ≫ pullback.fst f b =
      Spec.map (CommRingCat.ofHom (σ).toRingHom) ≫ (x ≫ pullback.fst f b) := by
  rw [Category.assoc, constantBaseChangeFrobenius_fst, ← Category.assoc]
  have hn := finiteFieldFrobenius_naturality (Spec (CommRingCat.of Ω)) k X
    (x ≫ pullback.fst f b)
  rw [finiteFieldFrobenius_spec] at hn
  exact hn.symm

private theorem frobeniusPowerSpecMap_succ (m : ℕ) :
    Spec.map (CommRingCat.ofHom (σ ^ (m + 1)).toRingHom) =
      Spec.map (CommRingCat.ofHom (σ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  change (σ ^ (m + 1)) a = σ ((σ ^ m) a)
  rw [pow_succ']
  rfl

/-- Every native power of relative Frobenius has the corresponding action
on original geometric points. -/
theorem constantBaseChangeFrobenius_pow_point_fst (m : ℕ)
    (x : Spec (.of Ω) ⟶ Y) :
    (x ≫ ((End.of F) ^ m).asHom) ≫ pullback.fst f b =
      Spec.map (CommRingCat.ofHom (σ ^ m).toRingHom) ≫
        (x ≫ pullback.fst f b) := by
  induction m with
  | zero =>
      change (x ≫ 𝟙 Y) ≫ pullback.fst f b =
        Spec.map (𝟙 (CommRingCat.of Ω)) ≫ (x ≫ pullback.fst f b)
      rw [Category.comp_id, Spec.map_id, Category.id_comp]
  | succ m ih =>
      rw [pow_succ', End.mul_asHom, ← Category.assoc x,
        constantBaseChangeFrobenius_point_fst, ih,
        frobeniusPowerSpecMap_succ, Category.assoc]

/-- The same native power fixes the extended constant base. -/
theorem constantBaseChangeFrobenius_pow_snd (m : ℕ) :
    ((End.of F) ^ m).asHom ≫ pullback.snd f b = pullback.snd f b := by
  induction m with
  | zero => exact Category.id_comp _
  | succ m ih =>
      rw [pow_succ', End.mul_asHom, Category.assoc,
        constantBaseChangeFrobenius_snd, ih]

end AlgebraicGeometry.Scheme
