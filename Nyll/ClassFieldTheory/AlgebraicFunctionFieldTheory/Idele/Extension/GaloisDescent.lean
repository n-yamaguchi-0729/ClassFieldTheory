/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.BaseChange
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormGalois
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Galois descent for principal ideles and fixed classes

The actual completed Galois action fixes every base-changed idele. An invariant
principal idele has its generating function in the base field, so base change on
idele classes is injective. Noether's Hilbert theorem 90 also supplies an invariant
representative of every invariant idele class.

The fixed-representative argument uses an actual place to detect equality of
diagonal functions. It does not assume a class-field-theoretic descent statement.
-/

noncomputable section

open AlgebraicCurve
open scoped AlgebraicCurve.Place

namespace FunctionField

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L]

namespace IdeleGroup

variable [Algebra.IsSeparable K L]

private theorem completionMapOver_baseChange (v : Place k K) (w : Place k L)
    (hw : w.restrict K = v) (a : IdeleGroup k K) :
    completionMapOver v w hw (a v : v.adicCompletion) =
      (baseChange (k := k) (K := K) (L := L) a w : w.adicCompletion) := by
  subst v
  rfl

/-- Field automorphisms over the base fix the actual base-changed idele. -/
@[simp]
theorem algAut_smul_baseChange (σ : L ≃ₐ[K] L) (a : IdeleGroup k K) :
    SemilinearAut.ofAlgAut (σ.restrictScalars k) •
        baseChange (k := k) (K := K) (L := L) a =
      baseChange (k := k) (K := K) (L := L) a := by
  let g : SemilinearAut k L := SemilinearAut.ofAlgAut (σ.restrictScalars k)
  apply IdeleGroup.ext
  intro w
  apply Units.ext
  change (placeCompletionRingEquiv g⁻¹ w).symm
      (baseChange (k := k) (K := K) (L := L) a (g⁻¹ • w) :
        (g⁻¹ • w).adicCompletion) =
    (baseChange (k := k) (K := K) (L := L) a w : w.adicCompletion)
  apply (placeCompletionRingEquiv g⁻¹ w).injective
  rw [RingEquiv.apply_symm_apply]
  have hrestrict : (g⁻¹ • w).restrict K = w.restrict K :=
    Place.restrict_ofAlgAut_smul σ.symm w
  have h := congrArg (fun f : (w.restrict K).adicCompletion →+*
      (g⁻¹ • w).adicCompletion => f (a (w.restrict K)))
    (completionMapOver_algAut σ.symm (w.restrict K) w rfl)
  change placeCompletionRingEquiv g⁻¹ w
      (completionMapOver (w.restrict K) w rfl (a (w.restrict K))) =
    completionMapOver (w.restrict K) (g⁻¹ • w)
      hrestrict (a (w.restrict K)) at h
  rw [completionMapOver_baseChange, completionMapOver_baseChange] at h
  exact h.symm

section Principal

variable [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- A single actual place detects equality of diagonal ideles. -/
theorem principalIdele_injective_of_nonempty [Nonempty (Place k L)] :
    Function.Injective (principalIdele k L) := by
  obtain ⟨w⟩ := ‹Nonempty (Place k L)›
  intro x y h
  apply Units.map_injective (algebraMap L w.adicCompletion).injective
  exact congrArg (component w) h

/-- An idele becomes principal in a finite Galois extension precisely when it was
already principal. The generating function descends through the fixed-field theorem. -/
theorem baseChange_mem_principalSubgroup_iff [IsGalois K L]
    [Nonempty (Place k L)] (a : IdeleGroup k K) :
    baseChange (k := k) (K := K) (L := L) a ∈ principalSubgroup k L ↔
      a ∈ principalSubgroup k K := by
  refine ⟨?_, baseChange_mem_principalSubgroup⟩
  rintro ⟨x, hx⟩
  have hfixed (σ : L ≃ₐ[K] L) : σ (x : L) = x := by
    have heq : principalIdele k L
        (Units.mapEquiv (SemilinearAut.toRingAut
          (SemilinearAut.ofAlgAut (σ.restrictScalars k))).toMulEquiv x) =
        principalIdele k L x := by
      rw [← smul_principalIdele, hx, algAut_smul_baseChange]
    exact congrArg Units.val (principalIdele_injective_of_nonempty heq)
  obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (x : L)).mpr hfixed
  have hy0 : y ≠ 0 := by
    intro h
    apply x.ne_zero
    rw [← hy, h, map_zero]
  let u : Kˣ := Units.mk0 y hy0
  have hu : Units.map (algebraMap K L) u = x := Units.ext hy
  refine ⟨u, baseChange_injective (k := k) (K := K) (L := L) ?_⟩
  rw [baseChange_principalIdele, hu, hx]

end Principal

end IdeleGroup

namespace IdeleClassGroup

variable [Algebra.IsSeparable K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- Every idele class from the base field is invariant under the completed action. -/
@[simp]
theorem algAut_smul_baseChange (σ : L ≃ₐ[K] L) (c : IdeleClassGroup k K) :
    SemilinearAut.ofAlgAut (σ.restrictScalars k) •
        baseChange (k := k) (K := K) (L := L) c =
      baseChange (k := k) (K := K) (L := L) c := by
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  rw [baseChange_mk, smul_mk, IdeleGroup.algAut_smul_baseChange]

/-- Inclusion of the actual idele class groups is injective for a finite Galois extension. -/
theorem baseChange_injective [IsGalois K L] :
    Function.Injective (baseChange (k := k) (K := K) (L := L)) := by
  classical
  intro c d h
  obtain ⟨a, rfl⟩ := mk_surjective (k := k) (K := K) c
  obtain ⟨b, rfl⟩ := mk_surjective (k := k) (K := K) d
  by_cases hn : Nonempty (Place k L)
  · have : Nonempty (Place k L) := hn
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply (IdeleGroup.baseChange_mem_principalSubgroup_iff (K := K) (L := L) (a / b)).mp
    rw [map_div]
    exact QuotientGroup.eq_iff_div_mem.mp h
  · have hab : IdeleGroup.baseChange (k := k) (K := K) (L := L) a =
        IdeleGroup.baseChange (k := k) (K := K) (L := L) b := by
      apply IdeleGroup.ext
      intro w
      exact (hn ⟨w⟩).elim
    exact congrArg (mk (k := k) (K := K)) (IdeleGroup.baseChange_injective hab)

end IdeleClassGroup

namespace IdeleGroup

variable [HasPrincipalDivisors k L] [Nonempty (Place k L)]

/-- Noether's Hilbert theorem 90 removes the principal cocycle of a fixed class.
The representative is fixed under the existing action on the actual completions. -/
theorem exists_fixed_representative_of_fixed_class (a : IdeleGroup k L)
    (ha : ∀ σ : L ≃ₐ[K] L,
      SemilinearAut.ofAlgAut (σ.restrictScalars k) •
          IdeleClassGroup.mk (k := k) (K := L) a =
        IdeleClassGroup.mk (k := k) (K := L) a) :
    ∃ a' : IdeleGroup k L,
      IdeleClassGroup.mk (k := k) (K := L) a' =
          IdeleClassGroup.mk (k := k) (K := L) a ∧
        ∀ σ : L ≃ₐ[K] L, SemilinearAut.ofAlgAut (σ.restrictScalars k) • a' = a' := by
  classical
  let g (σ : L ≃ₐ[K] L) : SemilinearAut k L :=
    SemilinearAut.ofAlgAut (σ.restrictScalars k)
  have hex (σ : L ≃ₐ[K] L) : ∃ x : Lˣ,
      principalIdele k L x = (g σ • a) / a :=
    QuotientGroup.eq_iff_div_mem.mp (ha σ)
  let f (σ : L ≃ₐ[K] L) : Lˣ := Classical.choose (hex σ)
  have hf_spec (σ : L ≃ₐ[K] L) :
      principalIdele k L (f σ) = (g σ • a) / a := Classical.choose_spec (hex σ)
  have hprincipal (σ : L ≃ₐ[K] L) (x : Lˣ) :
      principalIdele k L (σ • x) = g σ • principalIdele k L x :=
    (smul_principalIdele (g σ) x).symm
  have hg (σ τ : L ≃ₐ[K] L) : g (σ * τ) = g σ * g τ := rfl
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    apply principalIdele_injective_of_nonempty (k := k)
    rw [map_mul, hprincipal, hf_spec, hf_spec, hf_spec, smul_div', ← mul_smul, ← hg]
    exact (div_mul_div_cancel _ _ _).symm
  obtain ⟨β, hβ⟩ :=
    groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  let a' : IdeleGroup k L := a / principalIdele k L β
  have hratio (σ : L ≃ₐ[K] L) :
      (g σ • principalIdele k L β) / principalIdele k L β = (g σ • a) / a := by
    rw [← hprincipal, ← map_div, hβ σ, hf_spec σ]
  refine ⟨a', ?_, ?_⟩
  · apply QuotientGroup.eq_iff_div_mem.mpr
    refine ⟨β⁻¹, ?_⟩
    change (principalIdele k L β)⁻¹ = (a / principalIdele k L β) / a
    simpa only [div_mul_eq_div_div] using
      (div_mul_cancel_right a (principalIdele k L β)).symm
  · intro σ
    change g σ • (a / principalIdele k L β) = a / principalIdele k L β
    rw [smul_div']
    calc
      (g σ • a) / (g σ • principalIdele k L β) =
          ((g σ • a) / a) * (a / (g σ • principalIdele k L β)) :=
        (div_mul_div_cancel _ _ _).symm
      _ = ((g σ • principalIdele k L β) / principalIdele k L β) *
          (a / (g σ • principalIdele k L β)) := by rw [hratio σ]
      _ = a / principalIdele k L β := div_mul_div_cancel' _ _ _

end IdeleGroup

end FunctionField
