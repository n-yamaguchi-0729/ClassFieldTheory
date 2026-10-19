/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Automorphisms of the constant field on base-changed schemes

Coefficient automorphisms act on the actual pullback. Projection formulas and
the composition law are proved by the pullback universal property.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap k Ω))

/-- The spectrum of a coefficient automorphism fixes the original constant base. -/
theorem spec_coefficient_comp (σ : Ω ≃ₐ[k] Ω) :
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ b = b := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact σ.commutes a

/-- The actual twist of the constant base change by a coefficient automorphism. -/
def constantTwist (σ : Ω ≃ₐ[k] Ω) : pullback f b ≅ pullback f b := by
  have : IsIso (CommRingCat.ofHom σ.toRingHom) :=
    inferInstanceAs (IsIso σ.toRingEquiv.toCommRingCatIso.hom)
  exact asIso (pullback.map f b f b (𝟙 X)
    (Spec.map (CommRingCat.ofHom σ.toRingHom)) (𝟙 (Spec (CommRingCat.of k)))
    (by rw [Category.id_comp, Category.comp_id])
    (by rw [Category.comp_id]; exact (spec_coefficient_comp σ).symm))

/-- Coefficient twisting preserves the projection to the original scheme. -/
theorem constantTwist_fst (σ : Ω ≃ₐ[k] Ω) :
    (constantTwist f σ).hom ≫ pullback.fst f b = pullback.fst f b := by
  dsimp only [constantTwist, asIso]
  rw [pullback.lift_fst, Category.comp_id]

/-- Coefficient twisting induces the specified automorphism on the new constants. -/
theorem constantTwist_snd (σ : Ω ≃ₐ[k] Ω) :
    (constantTwist f σ).hom ≫ pullback.snd f b =
      pullback.snd f b ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  pullback.lift_snd _ _ _

/-- Twisting by the identity is the identity of the actual base change. -/
theorem constantTwist_one : constantTwist f (1 : Ω ≃ₐ[k] Ω) = Iso.refl _ := by
  apply Iso.ext
  apply pullback.hom_ext
  · rw [constantTwist_fst]
    exact (Category.id_comp _).symm
  · rw [constantTwist_snd]
    change pullback.snd f b ≫ Spec.map (𝟙 (CommRingCat.of Ω)) = 𝟙 _ ≫ pullback.snd f b
    rw [Spec.map_id, Category.comp_id, Category.id_comp]

/-- Coefficient multiplication becomes composition of the actual scheme twists. -/
theorem constantTwist_mul (σ τ : Ω ≃ₐ[k] Ω) :
    constantTwist f (σ * τ) = constantTwist f σ ≪≫ constantTwist f τ := by
  apply Iso.ext
  apply pullback.hom_ext
  · rw [constantTwist_fst]
    change pullback.fst f b =
      ((constantTwist f σ).hom ≫ (constantTwist f τ).hom) ≫ pullback.fst f b
    rw [Category.assoc, constantTwist_fst, constantTwist_fst]
  · rw [constantTwist_snd]
    change pullback.snd f b ≫ Spec.map (CommRingCat.ofHom (σ * τ).toRingHom) =
      ((constantTwist f σ).hom ≫ (constantTwist f τ).hom) ≫ pullback.snd f b
    rw [Category.assoc, constantTwist_snd, ← Category.assoc, constantTwist_snd,
      Category.assoc, ← Spec.map_comp]
    rfl

end AlgebraicGeometry.Scheme
