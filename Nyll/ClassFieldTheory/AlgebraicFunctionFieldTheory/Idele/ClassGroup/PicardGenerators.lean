/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic
import Nyll.AlgebraicCurves.Divisors.ClassGroup.PicardDegree
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.ClassGroup.ConstantExtension

/-!
# Finite generation of the full Picard group

The degree-zero subgroup is finite and the degree image is a subgroup of the integers.
Consequently the full Picard group is finitely generated, even when the base field is
smaller than the full field of constants.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve

variable (k K : Type*) [Field k] [Finite k] [Field K]
    [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
    [FunctionField k K] [HasPrincipalDivisors k K]

/-- The full Picard group is a finitely generated abelian group. -/
theorem finite_picardModule : Module.Finite ℤ (Pic k K) := by
  have : Finite (Pic0 k K) := finite_pic0 k K
  let f : Pic0 k K →ₗ[ℤ] Pic k K := (H1Gm.ofPic0 k K).toIntLinearMap
  let g : Pic k K →ₗ[ℤ] (H1Gm.degree k K).range :=
    (H1Gm.degree k K).rangeRestrict.toIntLinearMap
  have : Module.Finite ℤ (H1Gm.degree k K).range :=
    Module.Finite.of_injective (H1Gm.degree k K).range.subtype.toIntLinearMap
      Subtype.val_injective
  apply Module.Finite.of_exact (f := f) (g := g) ?_
    (H1Gm.degree k K).rangeRestrict_surjective
  intro x
  change (H1Gm.degree k K).rangeRestrict x = 0 ↔ ∃ y, H1Gm.ofPic0 k K y = x
  rw [← AddMonoidHom.mem_range, H1Gm.exact_ofPic0_degree]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- Finitely many places support representatives of every divisor class. -/
theorem exists_finset_picard_representatives :
    ∃ S : Finset (Place k K), ∀ c : Pic k K,
      ∃ D : Divisor k K, D.support ⊆ S ∧ H1Gm.mk D = c := by
  classical
  have : Module.Finite ℤ (Pic k K) := finite_picardModule k K
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := ℤ) (M := Pic k K)
  choose representative hrepresentative using H1Gm.mk_surjective (K := k) (F := K)
  let S : Finset (Place k K) := T.biUnion fun c => (representative c).support
  let q : Divisor k K →ₗ[ℤ] Pic k K :=
    (QuotientAddGroup.mk' Divisor.principal).toIntLinearMap
  let supported : Submodule ℤ (Divisor k K) := Finsupp.supported ℤ ℤ (S : Set (Place k K))
  have hmap : supported.map q = ⊤ := by
    apply top_unique
    rw [← hT]
    apply Submodule.span_le.mpr
    intro c hc
    refine ⟨representative c, ?_, hrepresentative c⟩
    change ↑(representative c).support ⊆ (S : Set (Place k K))
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨c, hc, hv⟩
  refine ⟨S, fun c => ?_⟩
  have hc : c ∈ supported.map q := hmap ▸ Submodule.mem_top
  obtain ⟨D, hD, hc⟩ := hc
  exact ⟨D, hD, hc⟩

end FunctionField
