/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.DegreeOne
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormTower

/-!
# Actual norm comparison across isomorphic field presentations

In a commuting square of field inclusions whose two vertical degrees are one,
idele-class base change commutes with the actual norm. The proof uses both
norm tower formulas and the actual degree-one norm inverses.
-/

noncomputable section

namespace FunctionField.IdeleClassGroup

variable {k K L F E : Type*} [Field k] [Field K] [Field L] [Field F] [Field E]
    [Algebra k K] [Algebra k L] [Algebra k F] [Algebra k E]
    [Algebra K L] [Algebra K F] [Algebra K E] [Algebra L E] [Algebra F E]
    [IsScalarTower k K L] [IsScalarTower k K F] [IsScalarTower k K E]
    [IsScalarTower k L E] [IsScalarTower k F E]
    [IsScalarTower K L E] [IsScalarTower K F E]
    [FiniteDimensional K L] [FiniteDimensional K F]
    [FiniteDimensional L E] [FiniteDimensional F E]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable F E] [IsGalois K F] [IsGalois L E]
    [AlgebraicCurve.HasPrincipalDivisors k K] [AlgebraicCurve.HasPrincipalDivisors k L]
    [AlgebraicCurve.HasPrincipalDivisors k F] [AlgebraicCurve.HasPrincipalDivisors k E]

/-- The actual class norm commutes with two compatible degree-one field inclusions. -/
theorem norm_baseChange_of_vertical_finrank_one
    (hF : Module.finrank K F = 1) (hE : Module.finrank L E = 1) (c : IdeleClassGroup k L) :
    baseChange (k := k) (K := K) (L := F) (norm (k := k) (K := K) (L := L) c) =
      norm (k := k) (K := F) (L := E) (baseChange (k := k) (K := L) (L := E) c) := by
  have hKEfinite : FiniteDimensional K E := Module.Finite.trans L E
  have hKEsep : Algebra.IsSeparable K E := Algebra.IsSeparable.trans K L E
  apply (baseChangeEquivOfFinrankOne (k := k) hF).symm.injective
  rw [baseChangeEquivOfFinrankOne_symm, baseChangeEquivOfFinrankOne_symm,
    norm_baseChange, hF, pow_one, norm_trans,
    ← norm_trans (k := k) (K := K) (L := L) (M := E), norm_baseChange, hE, pow_one]

/-- Actual norm subgroups are carried onto one another by a field presentation isomorphism. -/
theorem norm_range_map_baseChange_of_vertical_finrank_one
    (hF : Module.finrank K F = 1) (hE : Module.finrank L E = 1) :
    (norm (k := k) (K := K) (L := L)).range.map
        (baseChange (k := k) (K := K) (L := F)) =
      (norm (k := k) (K := F) (L := E)).range := by
  apply Subgroup.ext
  intro a
  constructor
  · rintro ⟨b, ⟨c, rfl⟩, rfl⟩
    exact ⟨baseChange (k := k) (K := L) (L := E) c,
      (norm_baseChange_of_vertical_finrank_one hF hE c).symm⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := (baseChange_bijective_of_finrank_one (k := k) hE).2 b
    exact ⟨norm (k := k) (K := K) (L := L) c, ⟨c, rfl⟩,
      norm_baseChange_of_vertical_finrank_one hF hE c⟩

-- The quotient group carries a bundled commutative structure; mathlib deliberately
-- does not infer its unbundled commutativity property from that structure.
local instance : IsMulCommutative (IdeleClassGroup k K) := ⟨⟨fun a b => mul_comm a b⟩⟩

/-- Degree-one changes of field presentation induce the actual norm-quotient isomorphism. -/
def normQuotientCongrOfVerticalFinrankOne
    (hF : Module.finrank K F = 1) (hE : Module.finrank L E = 1) :
    (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) ≃*
      (IdeleClassGroup k F ⧸ (norm (k := k) (K := F) (L := E)).range) :=
  QuotientGroup.congr _ _ (baseChangeEquivOfFinrankOne (k := k) (K := K) (L := F) hF)
    (norm_range_map_baseChange_of_vertical_finrank_one
      (k := k) (K := K) (L := L) (F := F) (E := E) hF hE)

/-- Norm-quotient transport sends a represented class to its actual base change. -/
theorem normQuotientCongrOfVerticalFinrankOne_mk
    (hF : Module.finrank K F = 1) (hE : Module.finrank L E = 1) (c : IdeleClassGroup k K) :
    normQuotientCongrOfVerticalFinrankOne (k := k) (K := K) (L := L) (F := F) (E := E)
        hF hE (QuotientGroup.mk c) =
      QuotientGroup.mk (baseChange (k := k) (K := K) (L := F) c) :=
  QuotientGroup.congr_mk _ _ (baseChangeEquivOfFinrankOne (k := k) (K := K) (L := F) hF)
    (norm_range_map_baseChange_of_vertical_finrank_one
      (k := k) (K := K) (L := L) (F := F) (E := E) hF hE) c

/-- Base change across a degree-one base field commutes with the norm from an upper field. -/
theorem baseChange_norm_of_base_finrank_one
    {k K F L : Type*} [Field k] [Field K] [Field F] [Field L]
    [Algebra k K] [Algebra k F] [Algebra k L]
    [Algebra K F] [Algebra K L] [Algebra F L]
    [IsScalarTower k K F] [IsScalarTower k K L] [IsScalarTower k F L]
    [IsScalarTower K F L] [FiniteDimensional K F] [FiniteDimensional K L]
    [FiniteDimensional F L] [IsGalois K F]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable F L]
    [AlgebraicCurve.HasPrincipalDivisors k K]
    [AlgebraicCurve.HasPrincipalDivisors k F]
    [AlgebraicCurve.HasPrincipalDivisors k L]
    (hF : Module.finrank K F = 1) (c : IdeleClassGroup k L) :
    IdeleClassGroup.baseChange (k := k) (K := K) (L := F)
        (IdeleClassGroup.norm (k := k) (K := K) (L := L) c) =
      IdeleClassGroup.norm (k := k) (K := F) (L := L) c := by
  apply (IdeleClassGroup.baseChangeEquivOfFinrankOne
    (k := k) (K := K) (L := F) hF).symm.injective
  rw [IdeleClassGroup.baseChangeEquivOfFinrankOne_symm,
    IdeleClassGroup.baseChangeEquivOfFinrankOne_symm,
    IdeleClassGroup.norm_baseChange, hF, pow_one, IdeleClassGroup.norm_trans]

end FunctionField.IdeleClassGroup
