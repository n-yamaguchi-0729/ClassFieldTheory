/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.ConstantTwist
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Coefficient twists in towers of constant fields

The actual iterated base change is identified with the single base change.
This identification commutes with automorphisms fixing the intermediate field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable (k E Ω : Type u) [Field k] [Field E] [Field Ω]
    [Algebra k E] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

local notation "b₀" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))
local notation "b₁" => Spec.map (CommRingCat.ofHom (algebraMap k E))
local notation "b₂" => Spec.map (CommRingCat.ofHom (algebraMap E Ω))

/-- Spectrum maps compose according to the actual field tower. -/
theorem spec_algebraMap_tower : b₂ ≫ b₁ = b₀ := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq k E Ω).symm

/-- The canonical isomorphism from iterated constant base change to a single base change. -/
def constantBaseChangeTowerIso : pullback (pullback.snd f b₁) b₂ ≅ pullback f b₀ :=
  pullbackLeftPullbackSndIso f b₁ b₂ ≪≫ pullback.congrHom rfl (spec_algebraMap_tower k E Ω)

/-- The tower isomorphism preserves the original scheme projection. -/
theorem constantBaseChangeTowerIso_fst :
    (constantBaseChangeTowerIso k E Ω f).hom ≫ pullback.fst f b₀ =
      pullback.fst (pullback.snd f b₁) b₂ ≫ pullback.fst f b₁ := by
  simp only [constantBaseChangeTowerIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_fst]

/-- The tower isomorphism preserves the final constant base. -/
theorem constantBaseChangeTowerIso_snd :
    (constantBaseChangeTowerIso k E Ω f).hom ≫ pullback.snd f b₀ =
      pullback.snd (pullback.snd f b₁) b₂ := by
  simp only [constantBaseChangeTowerIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
    pullbackLeftPullbackSndIso_hom_snd]

/-- The actual coefficient twists commute with the canonical tower isomorphism. -/
theorem constantBaseChangeTowerIso_twist (σ : Ω ≃ₐ[E] Ω) :
    (constantBaseChangeTowerIso k E Ω f).hom ≫ (constantTwist f (σ.restrictScalars k)).hom =
      (constantTwist (pullback.snd f b₁) σ).hom ≫
        (constantBaseChangeTowerIso k E Ω f).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, constantTwist_fst, Category.assoc,
      constantBaseChangeTowerIso_fst, ← Category.assoc, constantTwist_fst]
  · rw [Category.assoc, constantTwist_snd, ← Category.assoc,
      constantBaseChangeTowerIso_snd, Category.assoc, constantBaseChangeTowerIso_snd,
      constantTwist_snd]
    rfl

end AlgebraicGeometry.Scheme
