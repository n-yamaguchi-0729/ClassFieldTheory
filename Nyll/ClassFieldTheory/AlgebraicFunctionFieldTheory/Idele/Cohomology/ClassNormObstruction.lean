/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Cohomology.GlobalHilbert90
import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.GaloisDescent

/-!
# The actual class norm obstruction

The principal-idele homomorphism induces the concrete diagonal from the field
norm quotient to the idele norm quotient. For a cyclic extension its
injectivity is equivalent to vanishing of Tate H⁻¹ of the actual idele class
group. Idele Hilbert 90 proves the converse implication by adjusting an idele
representative by a principal norm preimage. No Hasse norm principle or
class-field axiom is assumed or asserted here.
-/

noncomputable section

namespace FunctionField.NormObstruction

open AlgebraicCurve
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] [IsGalois K L]
    [HasPrincipalDivisors k K] [HasPrincipalDivisors k L]

/-- The subgroup of actual global field norms on units. -/
def fieldNormSubgroup : Subgroup Kˣ :=
  (Units.map (Algebra.norm K : L →* K)).range

/-- The field units whose principal ideles are actual idele norms. -/
def principalNormSubgroup : Subgroup Kˣ :=
  (IdeleGroup.norm (k := k) (K := K) (L := L)).range.comap
    (IdeleGroup.principalIdele k K)

/-- An actual field norm gives an actual idele norm through the principal embedding. -/
theorem fieldNormSubgroup_le_principalNormSubgroup :
    fieldNormSubgroup (K := K) (L := L) ≤
      principalNormSubgroup (k := k) (K := K) (L := L) := by
  rintro x ⟨y, rfl⟩
  exact ⟨IdeleGroup.principalIdele k L y, IdeleGroup.norm_principalIdele y⟩

/-- The actual global-to-idele norm diagonal. -/
def hasseNormDiagonal :
    Kˣ ⧸ fieldNormSubgroup (K := K) (L := L) →*
      IdeleGroup k K ⧸ (IdeleGroup.norm (k := k) (K := K) (L := L)).range :=
  QuotientGroup.map (fieldNormSubgroup (K := K) (L := L))
    (IdeleGroup.norm (k := k) (K := K) (L := L)).range
    (IdeleGroup.principalIdele k K)
    (fun _ hx => fieldNormSubgroup_le_principalNormSubgroup hx)

/-- Evaluation of the actual norm diagonal on a field unit. -/
@[simp]
theorem hasseNormDiagonal_mk (x : Kˣ) :
    hasseNormDiagonal (k := k) (K := K) (L := L)
        (QuotientGroup.mk' (fieldNormSubgroup (K := K) (L := L)) x) =
      QuotientGroup.mk' (IdeleGroup.norm (k := k) (K := K) (L := L)).range
        (IdeleGroup.principalIdele k K x) :=
  rfl

/-- Injectivity of the actual diagonal means exactly that every principal
idele norm is a global field norm. -/
theorem hasseNormDiagonal_injective_iff :
    Function.Injective (hasseNormDiagonal (k := k) (K := K) (L := L)) ↔
      principalNormSubgroup (k := k) (K := K) (L := L) ≤
        fieldNormSubgroup (K := K) (L := L) := by
  constructor
  · intro hinj x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply hinj
    rw [map_one]
    change QuotientGroup.mk' (IdeleGroup.norm (k := k) (K := K) (L := L)).range
      (IdeleGroup.principalIdele k K x) = 1
    exact (QuotientGroup.eq_one_iff (IdeleGroup.principalIdele k K x)).mpr hx
  · intro hlocal
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm
    · intro q hq
      refine QuotientGroup.induction_on q ?_ hq
      intro x hx
      change QuotientGroup.mk' (fieldNormSubgroup (K := K) (L := L)) x = 1
      apply (QuotientGroup.eq_one_iff x).mpr
      apply hlocal
      exact (QuotientGroup.eq_one_iff (IdeleGroup.principalIdele k K x)).mp hx
    · exact bot_le

private theorem class_mk_eq_one_iff (a : IdeleGroup k L) :
    IdeleClassGroup.mk (k := k) (K := L) a = 1 ↔
      a ∈ IdeleGroup.principalSubgroup k L :=
  QuotientGroup.eq_one_iff a

private theorem norm_sigma_div (σ : L ≃ₐ[K] L) (b : IdeleGroup k L) :
    IdeleGroup.norm (k := k) (K := K) (L := L) ((σ • b) / b) = 1 := by
  apply (IdeleGroup.norm_eq_one_iff_tateNorm_eq_one (K := K) _).mpr
  change tateNorm (L ≃ₐ[K] L) (IdeleGroup k L) (σ • b * b⁻¹) = 1
  exact tateNorm_sigmaMinusOne_eq_one (G := L ≃ₐ[K] L) (A := IdeleGroup k L) σ b

/-- Injectivity of the actual norm diagonal removes every actual cyclic class
norm obstruction, by adjusting a representative and applying idele Hilbert 90. -/
theorem class_normKernel_le_augmentationSubgroup_of_diagonal_injective
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hinj : Function.Injective (hasseNormDiagonal (k := k) (K := K) (L := L))) :
    normKernelSubgroup (L ≃ₐ[K] L) (IdeleClassGroup k L) ≤
      augmentationSubgroup (L ≃ₐ[K] L) (IdeleClassGroup k L) σ := by
  intro c hc
  obtain ⟨a, rfl⟩ := IdeleClassGroup.mk_surjective c
  have hNa : IdeleGroup.norm (k := k) (K := K) (L := L) a ∈
      IdeleGroup.principalSubgroup k K := by
    apply (class_mk_eq_one_iff (k := k) (L := K) _).mp
    exact (IdeleClassGroup.norm_eq_one_iff_tateNorm_eq_one (K := K) _).mpr hc
  obtain ⟨x, hx⟩ := hNa
  have hxlocal : x ∈ principalNormSubgroup (k := k) (K := K) (L := L) :=
    ⟨a, hx.symm⟩
  obtain ⟨y, hy⟩ := (hasseNormDiagonal_injective_iff.mp hinj) hxlocal
  have hN : IdeleGroup.norm (k := k) (K := K) (L := L)
      (a / IdeleGroup.principalIdele k L y) = 1 := by
    rw [map_div, IdeleGroup.norm_principalIdele, hy, hx, div_self']
  obtain ⟨b, hb⟩ := IdeleGroup.exists_div_of_norm_eq_one σ hσ _ hN
  refine ⟨IdeleClassGroup.mk (k := k) (K := L) b, ?_⟩
  change σ • IdeleClassGroup.mk (k := k) (K := L) b *
    (IdeleClassGroup.mk (k := k) (K := L) b)⁻¹ = IdeleClassGroup.mk (k := k) (K := L) a
  have hp : IdeleClassGroup.mk (k := k) (K := L)
      (IdeleGroup.principalIdele k L y) = 1 :=
    (class_mk_eq_one_iff _).mpr ⟨y, rfl⟩
  have hm := congrArg (IdeleClassGroup.mk (k := k) (K := L)) hb
  rw [map_div, map_div, ← IdeleClassGroup.algAut_smul_mk, hp, div_one] at hm
  simpa only [div_eq_mul_inv] using hm

variable [Nonempty (Place k K)]

/-- If every class norm obstruction is an augmentation, each principal idele
norm is already a global field norm. The nonempty place hypothesis makes the
principal embedding faithful. -/
theorem principalNormSubgroup_le_fieldNormSubgroup_of_class_normKernel_le
    (σ : L ≃ₐ[K] L)
    (hclass : normKernelSubgroup (L ≃ₐ[K] L) (IdeleClassGroup k L) ≤
      augmentationSubgroup (L ≃ₐ[K] L) (IdeleClassGroup k L) σ) :
    principalNormSubgroup (k := k) (K := K) (L := L) ≤
      fieldNormSubgroup (K := K) (L := L) := by
  rintro x ⟨a, ha⟩
  have hc : IdeleClassGroup.mk (k := k) (K := L) a ∈
      normKernelSubgroup (L ≃ₐ[K] L) (IdeleClassGroup k L) := by
    apply (IdeleClassGroup.norm_eq_one_iff_tateNorm_eq_one (K := K) _).mp
    change IdeleClassGroup.mk (k := k) (K := K)
      (IdeleGroup.norm (k := k) (K := K) (L := L) a) = 1
    rw [ha]
    exact (class_mk_eq_one_iff _).mpr ⟨x, rfl⟩
  obtain ⟨d, hd⟩ := hclass hc
  obtain ⟨b, rfl⟩ := IdeleClassGroup.mk_surjective d
  change σ • IdeleClassGroup.mk (k := k) (K := L) b *
    (IdeleClassGroup.mk (k := k) (K := L) b)⁻¹ =
      IdeleClassGroup.mk (k := k) (K := L) a at hd
  have hd' : (σ • IdeleClassGroup.mk (k := k) (K := L) b) /
      IdeleClassGroup.mk (k := k) (K := L) b =
        IdeleClassGroup.mk (k := k) (K := L) a := by
    simpa only [div_eq_mul_inv] using hd
  have hprincipal : a / ((σ • b) / b) ∈ IdeleGroup.principalSubgroup k L := by
    apply (class_mk_eq_one_iff _).mp
    rw [map_div, map_div, ← IdeleClassGroup.algAut_smul_mk, hd', div_self']
  obtain ⟨y, hy⟩ := hprincipal
  refine ⟨y, ?_⟩
  apply IdeleGroup.principalIdele_injective_of_nonempty (k := k) (L := K)
  rw [← IdeleGroup.norm_principalIdele, hy, map_div, norm_sigma_div, div_one, ha]

/-- For a cyclic extension, injectivity of the actual global-to-idele norm
diagonal is exactly vanishing of Tate H⁻¹ of the actual idele class group. -/
theorem hasseNormDiagonal_injective_iff_class_herbrandHMinusOne_subsingleton
    (σ : L ≃ₐ[K] L) (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    Function.Injective (hasseNormDiagonal (k := k) (K := K) (L := L)) ↔
      Subsingleton (HerbrandHMinusOne (L ≃ₐ[K] L) (IdeleClassGroup k L) σ) := by
  rw [herbrandHMinusOne_subsingleton_iff_normKernel_le_augmentationSubgroup]
  constructor
  · exact class_normKernel_le_augmentationSubgroup_of_diagonal_injective σ hσ
  · intro hclass
    apply hasseNormDiagonal_injective_iff.mpr
    exact principalNormSubgroup_le_fieldNormSubgroup_of_class_normKernel_le σ hclass

end FunctionField.NormObstruction
