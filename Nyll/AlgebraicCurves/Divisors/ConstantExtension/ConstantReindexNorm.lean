/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ConstantExtension.ConstantReindex
import Nyll.AlgebraicCurves.Divisors.Norm.PicardNorm

/-!
# Actual Picard norms after changing the common constants

Reindexing places preserves restriction and residue field extension degrees.
Consequently it commutes with actual divisor pushforward and Picard norms.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable {k C K L : Type*} [Field k] [Field C] [Field K] [Field L]
    [Algebra k C] [Algebra k K] [Algebra C K] [IsScalarTower k C K]
    [Algebra k L] [Algebra C L] [IsScalarTower k C L]
    [Algebra K L] [IsScalarTower k K L] [IsScalarTower C K L]
    [Algebra.IsIntegral k C] [Algebra.IsIntegral K L]

/-- Actual divisor pushforward commutes with reindexing the common constant field. -/
theorem divisorConstantEquiv_pushforward (D : Divisor k L) :
    divisorConstantEquiv k C K (Divisor.pushforward K D) =
      Divisor.pushforward K (divisorConstantEquiv k C L D) := by
  induction D using Finsupp.induction with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | single_add v n D hv hn ih =>
    rw [map_add, map_add, map_add, map_add, ih, Divisor.pushforward_single]
    rw [divisorConstantEquiv_single, divisorConstantEquiv_single, Divisor.pushforward_single]
    have hv : (v.restrict K).extendConstants C = (v.extendConstants C).restrict K :=
      Place.ext rfl
    rw [hv]
    rfl

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [HasPrincipalDivisors k L] [HasPrincipalDivisors C L]

omit [Algebra.IsIntegral K L] in
/-- Actual Picard norm commutes with changing the common constant field. -/
theorem picConstantEquiv_norm (x : Pic k L) :
    picConstantEquiv k C K (Pic.norm (K := K) x) =
      Pic.norm (K := K) (picConstantEquiv k C L x) := by
  obtain ⟨D, rfl⟩ := H1Gm.mk_surjective x
  rw [Pic.norm_mk, picConstantEquiv_mk, picConstantEquiv_mk, Pic.norm_mk,
    divisorConstantEquiv_pushforward]

omit [Algebra.IsIntegral K L] in
/-- Changing the common constants preserves membership in the actual Picard norm image. -/
theorem mem_picardNorm_range_iff_constantEquiv (x : Pic k K) :
    x ∈ (Pic.norm (k := k) (K := K) (L := L)).range ↔
      picConstantEquiv k C K x ∈ (Pic.norm (k := C) (K := K) (L := L)).range := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨picConstantEquiv k C L y, (picConstantEquiv_norm y).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := (picConstantEquiv k C L).surjective y
    refine ⟨z, (picConstantEquiv k C K).injective ?_⟩
    rw [picConstantEquiv_norm]
    exact hy

end FunctionField
