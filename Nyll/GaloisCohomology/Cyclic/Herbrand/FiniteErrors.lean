/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Cyclic.Herbrand.Permutation.Module

/-!
# Herbrand quotients under maps with finite kernel and cokernel

An equivariant homomorphism with finite kernel and cokernel preserves both
definedness and the value of the Herbrand quotient. The proof factors the map
through its actual image and applies the existing short-exact-sequence theorem
twice. No isomorphism of the individual Tate groups is asserted.
-/

noncomputable section

namespace CyclicCohomology

open ProfiniteCohomology.Herbrand

section Actions

variable {G A B : Type*} [Group G] [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B]

private theorem ker_stable (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (g : G) (a : A) (ha : a ∈ f.ker) : g • a ∈ f.ker := by
  change f (g • a) = 1
  rw [hf, show f a = 1 from ha, smul_one]

private theorem range_stable (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (g : G) (b : B) (hb : b ∈ f.range) : g • b ∈ f.range := by
  obtain ⟨a, rfl⟩ := hb
  exact ⟨g • a, hf g a⟩

/-- Restrict the actual source action to the kernel of an equivariant map. -/
@[reducible]
def equivariantKerAction (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    MulDistribMulAction G f.ker :=
  stableSubgroupMulDistribMulAction f.ker (ker_stable f hf)

/-- Restrict the actual target action to the image of an equivariant map. -/
@[reducible]
def equivariantRangeAction (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    MulDistribMulAction G f.range :=
  stableSubgroupMulDistribMulAction f.range (range_stable f hf)

/-- Descend the actual target action to the cokernel of an equivariant map. -/
@[reducible]
def equivariantCokernelAction (f : A →* B)
    (hf : ∀ (g : G) (a : A), f (g • a) = g • f a) :
    MulDistribMulAction G (B ⧸ f.range) :=
  stableQuotientMulDistribMulAction f.range (range_stable f hf)

omit [MulDistribMulAction G A] [MulDistribMulAction G B] [Group G] in
private theorem ker_rangeRestrict_exact (f : A →* B) (a : A) :
    f.rangeRestrict a = 1 ↔ ∃ x : f.ker, f.ker.subtype x = a := by
  constructor
  · intro h
    exact ⟨⟨a, congrArg Subtype.val h⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact Subtype.ext x.2

end Actions

variable {G A B : Type} [Group G] [Fintype G] [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B]

/-- Finite kernel and cokernel preserve the finiteness of both low-degree Tate groups. -/
theorem herbrandQuotientDefined_iff_of_finite_kernel_cokernel
    (f : A →* B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a)
    [Finite f.ker] [Finite (B ⧸ f.range)]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    HerbrandQuotientDefined G A σ ↔ HerbrandQuotientDefined G B σ := by
  let : MulDistribMulAction G f.ker := equivariantKerAction f hf
  let : MulDistribMulAction G f.range := equivariantRangeAction f hf
  let : MulDistribMulAction G (B ⧸ f.range) := equivariantCokernelAction f hf
  have hK : HerbrandQuotientDefined G f.ker σ := ⟨inferInstance, inferInstance⟩
  have hQ : HerbrandQuotientDefined G (B ⧸ f.range) σ := ⟨inferInstance, inferInstance⟩
  have hi : ∀ (g : G) (a : f.ker), f.ker.subtype (g • a) = g • f.ker.subtype a :=
    fun _ _ => rfl
  have hj : ∀ (g : G) (a : A), f.rangeRestrict (g • a) = g • f.rangeRestrict a :=
    fun g a => Subtype.ext (hf g a)
  constructor
  · intro hA
    have hR := herbrandQuotientDefined_right_of_left_middle
      f.ker.subtype f.rangeRestrict hi hj (ker_rangeRestrict_exact f)
      f.ker.subtype_injective f.rangeRestrict_surjective σ hgen hK hA
    exact herbrandQuotientDefined_middle_of_left_right
      f.range.subtype (QuotientGroup.mk' f.range) (fun _ _ => rfl) (fun _ _ => rfl)
      (stableSubgroup_quotientMap_exact f.range) f.range.subtype_injective
      (QuotientGroup.mk'_surjective f.range) σ hgen hR hQ
  · intro hB
    have hR := herbrandQuotientDefined_left_of_middle_right
      f.range.subtype (QuotientGroup.mk' f.range) (fun _ _ => rfl) (fun _ _ => rfl)
      (stableSubgroup_quotientMap_exact f.range) f.range.subtype_injective
      (QuotientGroup.mk'_surjective f.range) σ hgen hB hQ
    exact herbrandQuotientDefined_middle_of_left_right
      f.ker.subtype f.rangeRestrict hi hj (ker_rangeRestrict_exact f)
      f.ker.subtype_injective f.rangeRestrict_surjective σ hgen hK hR

/-- An actual equivariant map with finite kernel and cokernel preserves the Herbrand quotient. -/
theorem herbrandQuotient_eq_of_finite_kernel_cokernel
    (f : A →* B) (hf : ∀ (g : G) (a : A), f (g • a) = g • f a)
    [Finite f.ker] [Finite (B ⧸ f.range)]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)] :
    herbrandQuotient (G := G) (A := A) σ = herbrandQuotient (G := G) (A := B) σ := by
  let : MulDistribMulAction G f.ker := equivariantKerAction f hf
  let : MulDistribMulAction G f.range := equivariantRangeAction f hf
  let : MulDistribMulAction G (B ⧸ f.range) := equivariantCokernelAction f hf
  have hi : ∀ (g : G) (a : f.ker), f.ker.subtype (g • a) = g • f.ker.subtype a :=
    fun _ _ => rfl
  have hj : ∀ (g : G) (a : A), f.rangeRestrict (g • a) = g • f.rangeRestrict a :=
    fun g a => Subtype.ext (hf g a)
  have hR := herbrandQuotientDefined_right_of_left_middle
    f.ker.subtype f.rangeRestrict hi hj (ker_rangeRestrict_exact f)
    f.ker.subtype_injective f.rangeRestrict_surjective σ hgen
    ⟨inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance⟩
  have : Finite (HerbrandH0 G f.range) := hR.1
  have : Finite (HerbrandHMinusOne G f.range σ) := hR.2
  have hA := herbrandQuotient_multiplicative_of_shortExact
    f.ker.subtype f.rangeRestrict hi hj (ker_rangeRestrict_exact f)
    f.ker.subtype_injective f.rangeRestrict_surjective σ hgen
  have hB := herbrandQuotient_multiplicative_of_shortExact
    f.range.subtype (QuotientGroup.mk' f.range) (fun _ _ => rfl) (fun _ _ => rfl)
    (stableSubgroup_quotientMap_exact f.range) f.range.subtype_injective
    (QuotientGroup.mk'_surjective f.range) σ hgen
  rw [herbrandQuotient_eq_one_of_finite_module (G := G) (A := f.ker) σ hgen,
    one_mul] at hA
  rw [herbrandQuotient_eq_one_of_finite_module (G := G) (A := B ⧸ f.range) σ hgen,
    mul_one] at hB
  exact hA.trans hB.symm

end CyclicCohomology
