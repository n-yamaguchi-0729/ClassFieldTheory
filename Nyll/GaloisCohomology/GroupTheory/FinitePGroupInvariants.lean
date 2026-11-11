/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod

/-!
# Trivial lines in finite characteristic-p representations of p-groups

The fixed-point counting theorem for p-group actions produces a nonzero
invariant vector. Its scalar line is an actual injective copy of the
trivial one-dimensional representation.
-/

@[expose] public section

noncomputable section

namespace Representation

variable {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod p) V] [Finite V] [Nontrivial V]

/-- Every nonzero finite characteristic-p representation of a p-group
has a nonzero invariant vector. -/
theorem exists_nonzero_fixed_of_isPGroup
    (ρ : Representation (ZMod p) G V) (hG : IsPGroup p G) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  let : MulAction G V :=
    { smul := fun g v => ρ g v
      one_smul := fun v =>
        congrArg (fun f : Module.End (ZMod p) V => f v) (map_one ρ)
      mul_smul := fun g h v =>
        congrArg (fun f : Module.End (ZMod p) V => f v) (map_mul ρ g h) }
  have : Fintype V := Fintype.ofFinite V
  have hpV : p ∣ Nat.card V := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p),
      ZMod.card]
    exact dvd_pow_self p (ne_of_gt (Module.finrank_pos (R := ZMod p) (M := V)))
  have hzero : (0 : V) ∈ MulAction.fixedPoints G V := by
    change ∀ g : G, ρ g 0 = 0
    intro g
    exact map_zero (ρ g)
  obtain ⟨v, hv, hne⟩ :=
    hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hpV hzero
  exact ⟨v, Ne.symm hne, hv⟩

/-- A nonzero finite characteristic-p representation of a p-group
contains an injective scalar line on which the group acts trivially. -/
theorem exists_injective_trivial_line_of_isPGroup
    (ρ : Representation (ZMod p) G V) (hG : IsPGroup p G) :
    ∃ f : ZMod p →ₗ[ZMod p] V, Function.Injective f ∧
      ∀ (g : G) (a : ZMod p), ρ g (f a) = f a := by
  obtain ⟨v, hv, hfix⟩ := exists_nonzero_fixed_of_isPGroup ρ hG
  let f : ZMod p →ₗ[ZMod p] V :=
    { toFun := fun a => a • v
      map_add' := fun a b => add_smul a b v
      map_smul' := fun a b => mul_smul a b v }
  refine ⟨f, ?_, ?_⟩
  · intro a b hab
    apply sub_eq_zero.mp
    have hz : (a - b) • v = 0 := by
      rw [sub_smul]
      exact sub_eq_zero.mpr hab
    exact (smul_eq_zero.mp hz).resolve_right hv
  · intro g a
    exact (map_smul (ρ g) a v).trans (congrArg (fun w : V => a • w) (hfix g))

end Representation

namespace Representation

variable {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G]
  [AddCommGroup V] [Module ℤ V] [Finite V] [Nontrivial V]

/-- The invariant-vector result applies to the actual integral coefficient
representation whenever its underlying group is killed by p. -/
theorem exists_nonzero_fixed_of_isPGroup_int
    (ρ : Representation ℤ G V) (hG : IsPGroup p G)
    (hp : ∀ v : V, p • v = 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  let : Module (ZMod p) V := AddCommGroup.zmodModule hp
  let σ : Representation (ZMod p) G V := by
    refine {
      toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap p
      map_one' := ?_
      map_mul' := ?_ }
    · apply LinearMap.ext
      intro v
      exact congrArg (fun f : Module.End ℤ V => f v) (map_one ρ)
    · intro g h
      apply LinearMap.ext
      intro v
      exact congrArg (fun f : Module.End ℤ V => f v) (map_mul ρ g h)
  exact exists_nonzero_fixed_of_isPGroup σ hG

end Representation

namespace Representation

private theorem isPGroup_range_of_ker_le {p : ℕ}
    {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : G →* K) (hker : f.ker ≤ g.ker)
    (hf : IsPGroup p f.range) : IsPGroup p g.range := by
  rintro ⟨b, a, rfl⟩
  obtain ⟨n, hn⟩ := hf ⟨f a, ⟨a, rfl⟩⟩
  refine ⟨n, Subtype.ext ?_⟩
  change (g a) ^ p ^ n = 1
  rw [← map_pow]
  apply hker
  change f (a ^ p ^ n) = 1
  rw [map_pow]
  exact congrArg Subtype.val hn

/-- Passing to an actual invariant-submodule quotient preserves a p-group
action image, without requiring the acting group itself to be a p-group. -/
theorem isPGroup_quotient_image {p : ℕ} {R G V : Type*}
    [CommRing R] [Group G] [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (W : Submodule R V)
    (hW : ∀ g, W ≤ W.comap (ρ g))
    (hρ : IsPGroup p ρ.asGroupHom.range) :
    IsPGroup p (ρ.quotient W hW).asGroupHom.range := by
  apply isPGroup_range_of_ker_le ρ.asGroupHom
    (ρ.quotient W hW).asGroupHom ?_ hρ
  intro g hg
  change ρ.asGroupHom g = 1 at hg
  change (ρ.quotient W hW).asGroupHom g = 1
  apply Units.ext
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := W.mkQ_surjective q
  have hv : ρ g v = v := by
    simpa only [asGroupHom_apply, Units.val_one, Module.End.one_apply] using
      congrArg (fun u : Units (Module.End R V) => (u : Module.End R V) v) hg
  change W.mkQ (ρ g v) = W.mkQ v
  exact congrArg W.mkQ hv

/-- A finite integral coefficient module with p-group action image and
annihilator p has a nonzero invariant vector. The acting group can be infinite. -/
theorem exists_nonzero_fixed_of_image_isPGroup_int
    {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℤ V] [Finite V] [Nontrivial V]
    (ρ : Representation ℤ G V) (hρ : IsPGroup p ρ.asGroupHom.range)
    (hp : ∀ v : V, p • v = 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  let H := ρ.asGroupHom.range
  let σ : Representation ℤ H V :=
    (Units.coeHom (Module.End ℤ V)).comp H.subtype
  obtain ⟨v, hv, hfix⟩ := exists_nonzero_fixed_of_isPGroup_int σ hρ hp
  refine ⟨v, hv, fun g => ?_⟩
  have h := hfix ⟨ρ.asGroupHom g, ⟨g, rfl⟩⟩
  change ((ρ.asGroupHom g : Units (Module.End ℤ V)) : Module.End ℤ V) v = v at h
  simpa only [asGroupHom_apply] using h

end Representation
