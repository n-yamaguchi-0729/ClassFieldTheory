/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Nyll.SchemeTheory.RingTheory.NormIdentities

/-!
# Congruence preserved by the finite free algebra norm

Reduction modulo a base ideal sends an element congruent to one to the
identity in the scalar-extended algebra. Base change of the determinant
then shows that its actual norm is congruent to one downstairs.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Algebra

/-- A finite free norm preserves congruence to one modulo an extended base ideal. -/
theorem norm_sub_one_mem_of_sub_one_mem_map
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S]
    (I : Ideal R) (x : S) (hx : x - 1 ∈ I.map (algebraMap R S)) :
    Algebra.norm R x - 1 ∈ I := by
  let f : S →ₐ[R] (R ⧸ I) ⊗[R] S := Algebra.TensorProduct.includeRight
  have hker : I.map (algebraMap R S) ≤ RingHom.ker f.toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change f (algebraMap R S a) = 0
    rw [f.commutes, IsScalarTower.algebraMap_apply R (R ⧸ I) ((R ⧸ I) ⊗[R] S),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hxQ : f x = 1 := by
    have h := hker hx
    rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h
    exact h
  have hnorm : Ideal.Quotient.mk I (Algebra.norm R x) = 1 := by
    calc
      Ideal.Quotient.mk I (Algebra.norm R x) = Algebra.norm (R ⧸ I) (f x) :=
        (Algebra.norm_one_tmul_eq_algebraMap_norm (R ⧸ I) x).symm
      _ = 1 := by rw [hxQ, map_one]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, map_one, hnorm, sub_self]

end Algebra
