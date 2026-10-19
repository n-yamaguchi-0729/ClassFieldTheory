/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Maps.Semilinear
import Mathlib.Tactic.Abel

/-!
# Invariant divisor classes from Picard Lang surjectivity

A surjective Lang operator on the actual degree-zero Picard group adjusts any
divisor by a degree-zero divisor so that its class is fixed. The resulting
invariance is expressed by an actual principal divisor.
-/

noncomputable section

namespace AlgebraicCurve

attribute [local instance]
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Every attained divisor degree has a fixed Picard class when the degree-zero Lang map is onto. -/
theorem exists_fixed_divisor_class_of_pic0_lang (g : SemilinearAut K F)
    (hLang : Function.Surjective (fun x : Pic0 K F => g • x - x)) (D : Divisor K F) :
    ∃ D' : Divisor K F, Divisor.degree D' = Divisor.degree D ∧
      (g • D' - D').IsPrincipal := by
  let δ : Divisor.degZero (K := K) (F := F) :=
    ⟨g • D - D, by
      rw [Divisor.mem_degZero, map_sub, SemilinearAut.degree_smul, sub_self]⟩
  obtain ⟨y, hy⟩ := hLang (Pic0.mk δ)
  change g • y - y = Pic0.mk δ at hy
  obtain ⟨E, hE⟩ := Pic0.mk_surjective y
  let dE := SemilinearAut.degZeroSMulHom g E - E
  have hp : Pic0.mk dE = Pic0.mk δ := by
    change g • Pic0.mk E - Pic0.mk E = Pic0.mk δ
    rw [hE]
    exact hy
  have hp' : dE - δ ∈ (Divisor.principal (K := K) (F := F)).addSubgroupOf
      (Divisor.degZero (K := K) (F := F)) := QuotientAddGroup.eq_iff_sub_mem.mp hp
  have hprincipal : ((dE - δ : Divisor.degZero (K := K) (F := F)) : Divisor K F) ∈
      Divisor.principal := hp'
  refine ⟨D - (E : Divisor K F), ?_, ?_⟩
  · rw [map_sub, show Divisor.degree (E : Divisor K F) = 0 from E.property, sub_zero]
  · apply Divisor.mem_principal.mp
    have hn := (Divisor.principal (K := K) (F := F)).neg_mem hprincipal
    have heq : g • (D - (E : Divisor K F)) - (D - (E : Divisor K F)) =
        -((dE - δ : Divisor.degZero (K := K) (F := F)) : Divisor K F) := by
      change g • (D - (E : Divisor K F)) - (D - (E : Divisor K F)) =
        -((g • (E : Divisor K F) - (E : Divisor K F)) - (g • D - D))
      rw [smul_sub]
      abel
    exact heq.symm ▸ hn

end AlgebraicCurve
