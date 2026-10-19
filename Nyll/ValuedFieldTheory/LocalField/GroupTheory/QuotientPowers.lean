/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Power classes modulo a subgroup

The third isomorphism theorem identifies the quotient by a subgroup and
n-th powers with n-th power classes in the original subgroup quotient.
-/

noncomputable section
namespace LocalFieldTheory

variable (G : Type*) [CommGroup G]

/-- Taking power classes commutes with first quotienting by a subgroup. -/
def quotientSupRangePowEquiv (H : Subgroup G) (n : ℕ) :
    G ⧸ (H ⊔ (powMonoidHom (α := G) n).range) ≃
      ((G ⧸ H) ⧸ (MonoidHom.range (G := G ⧸ H) (N := G ⧸ H) (powMonoidHom (α := G ⧸ H) n))) := by
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  have hpow : ((powMonoidHom (α := G) n).range).map q =
      (MonoidHom.range (G := G ⧸ H) (N := G ⧸ H) (powMonoidHom (α := G ⧸ H) n)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨q z, (map_pow q z n).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective H y
      exact ⟨z ^ n, ⟨z, rfl⟩, map_pow q z n⟩
  have hmap : (H ⊔ (powMonoidHom (α := G) n).range).map q =
      (MonoidHom.range (G := G ⧸ H) (N := G ⧸ H) (powMonoidHom (α := G ⧸ H) n)) := by
    rw [Subgroup.map_sup, hpow]
    have hz : H.map q = ⊥ := QuotientGroup.map_mk'_self H
    rw [hz, bot_sup_eq]
  exact ((QuotientGroup.quotientQuotientEquivQuotient H
      (H ⊔ (powMonoidHom (α := G) n).range) le_sup_left).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hmap)).toEquiv

end LocalFieldTheory
