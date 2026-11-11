/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Images of inertia at translated primes
-/

@[expose] public section

namespace EtaleFundamentalGroups.Inertia

open scoped Pointwise

/-- Translating the original prime induces positive conjugation in every group image. -/
theorem inertia_smul_map
    {M G R : Type*} [Group M] [Group G] [Ring R] [MulSemiringAction M R]
    (Q : Ideal R) (σ : M) (q : M →* G) :
    ((σ • Q).inertia M).map q =
      ((Q.inertia M).map q).map (MulAut.conj (q σ)) := by
  rw [Ideal.inertia_smul, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext τ
  change q (σ * τ * σ⁻¹) = q σ * q τ * (q σ)⁻¹
  simp only [map_mul, map_inv]

end EtaleFundamentalGroups.Inertia
