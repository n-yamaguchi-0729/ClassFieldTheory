/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.FixedIdeles
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormCohomology

/-!
# Fixed groups and the actual function-field norm quotients

Trace-one descent and Hilbert 90 identify the actual base idele groups with the
Galois fixed groups. Under these equivalences the actual norm images become the
Tate norm images. The existing quotient-group construction then identifies the
actual norm quotients with degree-zero Tate cohomology.
-/

noncomputable section

namespace FunctionField

open AlgebraicCurve
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

namespace IdeleGroup

/-- Actual Galois descent makes every fixed idele the inclusion of a base idele. -/
theorem baseChangeToFixed_surjective :
    Function.Surjective (baseChangeToFixed (k := k) (K := K) (L := L)) := by
  intro a
  obtain ⟨b, hb⟩ := exists_baseChange_of_algAut_fixed (k := k) (K := K) (L := L) a.1 a.2
  exact ⟨b, Subtype.ext hb⟩

/-- The base idele group is the fixed subgroup of the actual completed action. -/
def baseChangeEquivFixed :
    IdeleGroup k K ≃* fixedSubgroup (L ≃ₐ[K] L) (IdeleGroup k L) :=
  MulEquiv.ofBijective (baseChangeToFixed (k := k) (K := K) (L := L))
    ⟨baseChangeToFixed_injective, baseChangeToFixed_surjective⟩

/-- The fixed-group equivalence is the existing base-change map on components. -/
@[simp]
theorem coe_baseChangeEquivFixed_apply (a : IdeleGroup k K) :
    (baseChangeEquivFixed (k := k) (K := K) (L := L) a : IdeleGroup k L) =
      baseChange (k := k) (K := K) (L := L) a :=
  rfl

/-- The fixed-group equivalence carries the actual norm image to the Tate norm image. -/
theorem norm_range_map_baseChangeEquivFixed :
    (norm (k := k) (K := K) (L := L)).range.map
        (baseChangeEquivFixed (k := k) (K := K) (L := L)).toMonoidHom =
      (tateNormSubgroup (L ≃ₐ[K] L) (IdeleGroup k L)).subgroupOf
        (fixedSubgroup (L ≃ₐ[K] L) (IdeleGroup k L)) := by
  apply Subgroup.ext
  intro a
  constructor
  · rintro ⟨b, ⟨c, rfl⟩, hb⟩
    change ∃ c : IdeleGroup k L,
      tateNorm (L ≃ₐ[K] L) (IdeleGroup k L) c = (a : IdeleGroup k L)
    refine ⟨c, ?_⟩
    rw [← baseChange_norm_eq_tateNorm]
    exact congrArg Subtype.val hb
  · intro ha
    change ∃ c : IdeleGroup k L,
      tateNorm (L ≃ₐ[K] L) (IdeleGroup k L) c = (a : IdeleGroup k L) at ha
    obtain ⟨c, hc⟩ := ha
    refine ⟨norm (k := k) (K := K) (L := L) c, ⟨c, rfl⟩, ?_⟩
    apply Subtype.ext
    change baseChange (k := k) (K := K) (L := L)
      (norm (k := k) (K := K) (L := L) c) = (a : IdeleGroup k L)
    rw [baseChange_norm_eq_tateNorm]
    exact hc

/-- The actual idele norm quotient is degree-zero Tate cohomology. -/
def normQuotientEquivHerbrandH0 :
    (IdeleGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) ≃*
      HerbrandH0 (L ≃ₐ[K] L) (IdeleGroup k L) :=
  (QuotientGroup.congr _ _ (baseChangeEquivFixed (k := k) (K := K) (L := L))
    norm_range_map_baseChangeEquivFixed).trans
      (HerbrandH0.equiv (G := L ≃ₐ[K] L) (A := IdeleGroup k L)).symm

/-- The norm-quotient equivalence sends an idele to the Tate class of its inclusion. -/
@[simp]
theorem normQuotientEquivHerbrandH0_mk (a : IdeleGroup k K) :
    normQuotientEquivHerbrandH0 (k := k) (K := K) (L := L)
        (QuotientGroup.mk' (norm (k := k) (K := K) (L := L)).range a) =
      HerbrandH0.mk (baseChangeToFixed (k := k) (K := K) (L := L) a) :=
  rfl

end IdeleGroup

namespace IdeleClassGroup

/-- Hilbert 90 and actual idele descent give all fixed classes by base change. -/
theorem baseChangeToFixed_surjective :
    Function.Surjective (baseChangeToFixed (k := k) (K := K) (L := L)) := by
  intro c
  obtain ⟨b, hb⟩ := exists_baseChange_of_algAut_fixed (k := k) (K := K) (L := L) c.1 c.2
  exact ⟨b, Subtype.ext hb⟩

/-- The base idele class group is the fixed group of the actual extension action. -/
def baseChangeEquivFixed :
    IdeleClassGroup k K ≃* fixedSubgroup (L ≃ₐ[K] L) (IdeleClassGroup k L) :=
  MulEquiv.ofBijective (baseChangeToFixed (k := k) (K := K) (L := L))
    ⟨baseChangeToFixed_injective, baseChangeToFixed_surjective⟩

/-- The fixed-class equivalence is the established inclusion on idele classes. -/
@[simp]
theorem coe_baseChangeEquivFixed_apply (c : IdeleClassGroup k K) :
    (baseChangeEquivFixed (k := k) (K := K) (L := L) c : IdeleClassGroup k L) =
      baseChange (k := k) (K := K) (L := L) c :=
  rfl

/-- Actual class norms correspond to Tate norms inside the fixed group. -/
theorem norm_range_map_baseChangeEquivFixed :
    (norm (k := k) (K := K) (L := L)).range.map
        (baseChangeEquivFixed (k := k) (K := K) (L := L)).toMonoidHom =
      (tateNormSubgroup (L ≃ₐ[K] L) (IdeleClassGroup k L)).subgroupOf
        (fixedSubgroup (L ≃ₐ[K] L) (IdeleClassGroup k L)) := by
  apply Subgroup.ext
  intro a
  constructor
  · rintro ⟨b, ⟨c, rfl⟩, hb⟩
    change ∃ c : IdeleClassGroup k L,
      tateNorm (L ≃ₐ[K] L) (IdeleClassGroup k L) c = (a : IdeleClassGroup k L)
    refine ⟨c, ?_⟩
    rw [← baseChange_norm_eq_tateNorm]
    exact congrArg Subtype.val hb
  · intro ha
    change ∃ c : IdeleClassGroup k L,
      tateNorm (L ≃ₐ[K] L) (IdeleClassGroup k L) c = (a : IdeleClassGroup k L) at ha
    obtain ⟨c, hc⟩ := ha
    refine ⟨norm (k := k) (K := K) (L := L) c, ⟨c, rfl⟩, ?_⟩
    apply Subtype.ext
    change baseChange (k := k) (K := K) (L := L)
      (norm (k := k) (K := K) (L := L) c) = (a : IdeleClassGroup k L)
    rw [baseChange_norm_eq_tateNorm]
    exact hc

/-- The actual norm image is normal in the commutative idele class group. -/
instance norm_range_normal : (norm (k := k) (K := K) (L := L)).range.Normal where
  conj_mem a ha g := by
    simpa only [mul_comm g a, mul_assoc, mul_inv_cancel, mul_one] using ha

/-- The actual idele class norm quotient is degree-zero Tate cohomology. -/
def normQuotientEquivHerbrandH0 :
    (IdeleClassGroup k K ⧸ (norm (k := k) (K := K) (L := L)).range) ≃*
      HerbrandH0 (L ≃ₐ[K] L) (IdeleClassGroup k L) :=
  (QuotientGroup.congr _ _ (baseChangeEquivFixed (k := k) (K := K) (L := L))
    norm_range_map_baseChangeEquivFixed).trans
      (HerbrandH0.equiv (G := L ≃ₐ[K] L) (A := IdeleClassGroup k L)).symm

/-- The equivalence sends a base idele class to the Tate class of its inclusion. -/
@[simp]
theorem normQuotientEquivHerbrandH0_mk (c : IdeleClassGroup k K) :
    normQuotientEquivHerbrandH0 (k := k) (K := K) (L := L)
        (QuotientGroup.mk' (norm (k := k) (K := K) (L := L)).range c) =
      HerbrandH0.mk (baseChangeToFixed (k := k) (K := K) (L := L) c) :=
  rfl

end IdeleClassGroup

end FunctionField
