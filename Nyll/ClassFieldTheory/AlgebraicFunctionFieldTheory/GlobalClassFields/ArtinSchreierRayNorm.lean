/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ArtinSchreierLocalConductor
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.GlobalClassFields.ArtinSchreierUnramified
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Fields.FiniteExtensionCurve
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormOpen
import Nyll.AlgebraicCurves.Places.Rational.Basic

/-!
# Ray congruences are actual norms from bounded Artin–Schreier extensions

Local conductor bounds supply norm preimages at the support of the modulus.
Outside that finite support the extension is unramified, so integral norm
preimages assemble to an actual idele and then an actual idele class norm.
-/

noncomputable section
open AlgebraicCurve
open scoped WithZero AlgebraicCurve.Place

namespace FunctionField

variable {k K L : Type} [Field k] [Finite k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- A parameter bounded by p times an effective modulus gives an extension
whose actual norm group contains the corresponding ray subgroup. -/
theorem artinSchreier_rayClassSubgroup_le_norm
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (m : RayClass.Modulus k K) (a : K) (β : L)
    (hβ : β ^ p - β = algebraMap K L a) (hgen : Algebra.adjoin K {β} = ⊤)
    (ha : ∀ v : Place k K, v.adicValuation a ≤ WithZero.exp ((p * m v : ℕ) : ℤ)) :
    RayClass.rayClassSubgroup (p • m) ≤
      (IdeleClassGroup.norm (k := k) (K := K) (L := L)).range := by
  classical
  let presentation := ClassFieldTheory.FunctionField.finiteExtensionRatFuncAlgebra k K L
  let aRL : Algebra (RatFunc k) L := presentation.val
  have hkRL : IsScalarTower k (RatFunc k) L := presentation.property.1
  have hfunction : FunctionField k L := presentation.property.2
  intro c hc
  obtain ⟨u, hu, rfl⟩ := hc
  have hunit (v : Place k K) : u v ∈ RayClass.localHigherUnitGroup v (p * m v) := by
    simpa only [Finsupp.smul_apply, smul_eq_mul] using hu v
  have hnormOver (v : Place k K) (w : Place k L) (hw : w.restrict K = v) :
      u v ∈ (IdeleGroup.localNormOver v w hw).range := by
    subst v
    exact artinSchreier_localHigherUnitGroup_le_norm p w a β hβ hgen
      (m (w.restrict K)) (ha (w.restrict K)) (hunit (w.restrict K))
  choose w hw using fun v : Place k K => Place.exists_restrict_eq (M := L) v
  have hpre (v : Place k K) : ∃ z : IdeleGroup k L,
      IdeleGroup.normComponent (k := k) (K := K) (L := L) v z = u v ∧
      (v ∉ m.support → IdeleGroup.fiberProjection (L := L) v z ∈
        IdeleGroup.fiberIntegralUnits (L := L) v) := by
    by_cases hv : v ∈ m.support
    · obtain ⟨x, hx⟩ := hnormOver v (w v) (hw v)
      exact ⟨IdeleGroup.placeIdele (w v) x,
        (IdeleGroup.normComponent_placeIdele v (w v) (hw v) x).trans hx,
        fun hn => (hn hv).elim⟩
    · have hm : m v = 0 := Finsupp.notMem_support_iff.mp hv
      have haint : a ∈ ((w v).restrict K).toValuationSubring := by
        apply ((w v).restrict K).mem_iff_adicValuation_le_one.mpr
        simpa only [hw v, hm, Nat.mul_zero, Nat.cast_zero, WithZero.exp_zero] using ha v
      have he : (w v).ramificationIndex K = 1 :=
        artinSchreier_ramificationIndex_eq_one p a β hβ hgen (w v) haint
      obtain ⟨x, hxint, hx⟩ :=
        IdeleGroup.exists_integral_localNormOver_eq_of_ramificationIndex_eq_one
          v (w v) (hw v) he (u v)
          (RayClass.localHigherUnitGroup_le_localUnits v (p * m v) (hunit v))
      exact ⟨IdeleGroup.placeIdele (w v) x,
        (IdeleGroup.normComponent_placeIdele v (w v) (hw v) x).trans hx,
        fun _ => IdeleGroup.fiberProjection_placeIdele_mem_integral v (w v) x hxint⟩
  choose z hz hzi using hpre
  have haway : ∀ᶠ v : Place k K in Filter.cofinite, v ∉ m.support :=
    m.support.finite_toSet.compl_mem_cofinite
  obtain ⟨y, hy⟩ := IdeleGroup.mem_norm_range_of_normComponent_preimages u z hz
    (haway.mono fun v hv => hzi v hv)
  exact ⟨IdeleClassGroup.mk (k := k) (K := L) y,
    congrArg (IdeleClassGroup.mk (k := k) (K := K)) hy⟩

end FunctionField
