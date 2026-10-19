/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic

/-!
# Tate quotients for a trivial action

For an actual trivial action the norm is the power by the group order.
The two low-degree Tate groups are therefore the power quotient and power
kernel. These comparisons retain the supplied action and do not reconstruct it.
-/

noncomputable section

namespace CyclicCohomology.ProfiniteCohomology.Herbrand

variable {G A : Type*} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]

/-- The norm for a trivial action is the power by the order of the group. -/
theorem tateNormHom_eq_powMonoidHom_of_trivial
    (htriv : ∀ (g : G) (a : A), g • a = a) :
    tateNormHom (G := G) (A := A) = powMonoidHom (Fintype.card G) := by
  ext a
  simp only [tateNormHom_apply, tateNorm, htriv, Finset.prod_const,
    Finset.card_univ, powMonoidHom_apply]

/-- Degree-zero Tate cohomology of a trivial action is the actual power quotient. -/
def herbrandH0EquivPowQuotient_of_trivial
    (htriv : ∀ (g : G) (a : A), g • a = a) :
    HerbrandH0 G A ≃* A ⧸ (powMonoidHom (α := A) (Fintype.card G)).range := by
  let e : fixedSubgroup G A ≃* A :=
    MulEquiv.ofBijective (fixedSubgroup G A).subtype
      ⟨Subtype.val_injective, fun a => ⟨⟨a, fun g => htriv g a⟩, rfl⟩⟩
  apply (HerbrandH0.equiv (G := G) (A := A)).trans
  apply QuotientGroup.congr _ _ e
  change ((tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)).map
    (fixedSubgroup G A).subtype = (powMonoidHom (Fintype.card G)).range
  rw [Subgroup.map_subgroupOf_eq_of_le tateNormSubgroup_le_fixedSubgroup]
  exact congrArg MonoidHom.range (tateNormHom_eq_powMonoidHom_of_trivial htriv)

/-- Degree-minus-one Tate cohomology of a trivial action is the actual power kernel. -/
def herbrandHMinusOneEquivPowKernel_of_trivial
    (htriv : ∀ (g : G) (a : A), g • a = a) (σ : G) :
    HerbrandHMinusOne G A σ ≃* (powMonoidHom (α := A) (Fintype.card G)).ker := by
  have haug : augmentationSubgroup G A σ = ⊥ := by
    apply le_antisymm
    · rintro a ⟨b, rfl⟩
      rw [Subgroup.mem_bot]
      change σ • b * b⁻¹ = 1
      rw [htriv, mul_inv_cancel]
    · exact bot_le
  have hker : normKernelSubgroup G A = (powMonoidHom (Fintype.card G)).ker :=
    congrArg MonoidHom.ker (tateNormHom_eq_powMonoidHom_of_trivial htriv)
  exact (HerbrandHMinusOne.equiv (G := G) (A := A) σ).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (by rw [haug, Subgroup.bot_subgroupOf])).trans
        ((QuotientGroup.quotientBot).trans (MulEquiv.subgroupCongr hker)))

end CyclicCohomology.ProfiniteCohomology.Herbrand
