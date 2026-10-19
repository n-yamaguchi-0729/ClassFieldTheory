/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.Idele.Extension.NormCohomology
import Nyll.GaloisCohomology.Cyclic.MultiplicativeHilbert90

/-!
# Cyclic Hilbert 90 for actual principal ideles

The extension action preserves the actual principal subgroup. A principal idele
of norm one is the coboundary of another principal idele: evaluation at a place
reduces this to field Hilbert 90, while an empty set of places gives the trivial
group. Consequently the principal term in the idele class sequence has vanishing
degree-minus-one Tate cohomology for a cyclic extension.
-/

noncomputable section

namespace FunctionField.IdeleGroup

open AlgebraicCurve
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [HasPrincipalDivisors k L]

/-- The actual principal subgroup inherits the completed extension action. -/
instance principalGaloisMulDistribMulAction :
    MulDistribMulAction (L ≃ₐ[K] L) (principalSubgroup k L) where
  smul σ a := ⟨σ • (a : IdeleGroup k L),
    smul_mem_principalSubgroup (SemilinearAut.ofAlgAut (σ.restrictScalars k)) a.2⟩
  one_smul a := Subtype.ext (one_smul (L ≃ₐ[K] L) (a : IdeleGroup k L))
  mul_smul σ τ a := Subtype.ext (mul_smul σ τ (a : IdeleGroup k L))
  smul_one σ := Subtype.ext (smul_one σ)
  smul_mul σ a b := Subtype.ext (smul_mul' σ (a : IdeleGroup k L) (b : IdeleGroup k L))

/-- Inclusion of principal ideles is equivariant for the actual extension action. -/
@[simp]
theorem coe_principal_algAut_smul (σ : L ≃ₐ[K] L) (a : principalSubgroup k L) :
    ((σ • a : principalSubgroup k L) : IdeleGroup k L) = σ • (a : IdeleGroup k L) :=
  rfl

/-- The extension action on a principal idele is the original action on its function. -/
theorem algAut_smul_principalIdele (σ : L ≃ₐ[K] L) (x : Lˣ) :
    σ • principalIdele k L x = principalIdele k L (σ • x) :=
  smul_principalIdele (SemilinearAut.ofAlgAut (σ.restrictScalars k)) x

variable [FiniteDimensional K L] [IsGalois K L] [HasPrincipalDivisors k K]

/-- Every actual norm-one principal idele is a coboundary inside the principal subgroup. -/
theorem exists_principal_div_of_norm_eq_one (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a : IdeleGroup k L) (ha : a ∈ principalSubgroup k L)
    (hN : norm (k := k) (K := K) (L := L) a = 1) :
    ∃ b : IdeleGroup k L, b ∈ principalSubgroup k L ∧ (σ • b) / b = a := by
  classical
  by_cases hplaces : Nonempty (Place k L)
  · obtain ⟨w⟩ := hplaces
    have : Nonempty (Place k K) := ⟨w.restrict K⟩
    obtain ⟨x, rfl⟩ := ha
    have hNx : Units.map (Algebra.norm K) x = 1 := by
      apply principalIdele_injective_of_nonempty (k := k) (L := K)
      rw [map_one, ← norm_principalIdele]
      exact hN
    have hx : Algebra.norm K (x : L) = 1 := congrArg Units.val hNx
    obtain ⟨y, hy⟩ := CyclicCohomology.exists_unit_coboundary_of_norm_eq_one
      (K := K) (L := L) σ hσ x hx
    refine ⟨principalIdele k L y, ⟨y, rfl⟩, ?_⟩
    rw [algAut_smul_principalIdele, ← map_div, hy]
  · have ha1 : a = 1 := by
      apply IdeleGroup.ext
      intro w
      exact False.elim (hplaces ⟨w⟩)
    exact ⟨1, (principalSubgroup k L).one_mem, by rw [ha1, smul_one, div_self']⟩

/-- In the principal subgroup every Tate norm-kernel element is an augmentation element. -/
theorem principal_normKernel_le_augmentationSubgroup (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    normKernelSubgroup (L ≃ₐ[K] L) (principalSubgroup k L) ≤
      augmentationSubgroup (L ≃ₐ[K] L) (principalSubgroup k L) σ := by
  intro a ha
  have haN : tateNorm (L ≃ₐ[K] L) (principalSubgroup k L) a = 1 := ha
  have hN : norm (k := k) (K := K) (L := L) (a : IdeleGroup k L) = 1 := by
    apply (norm_eq_one_iff_tateNorm_eq_one (k := k) (K := K) (L := L) a.1).mpr
    calc
      tateNorm (L ≃ₐ[K] L) (IdeleGroup k L) (a : IdeleGroup k L) =
          (principalSubgroup k L).subtype
            (tateNorm (L ≃ₐ[K] L) (principalSubgroup k L) a) :=
        (map_tateNorm (G := L ≃ₐ[K] L)
          (principalSubgroup k L).subtype (fun _ _ => rfl) a).symm
      _ = 1 := by rw [haN, map_one]
  obtain ⟨b, hb, hdiv⟩ := exists_principal_div_of_norm_eq_one σ hσ a.1 a.2 hN
  refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
  change σ • b * b⁻¹ = (a : IdeleGroup k L)
  simpa only [div_eq_mul_inv] using hdiv

/-- Cyclic Hilbert 90 identifies the two subgroups in the actual principal Tate quotient. -/
theorem principal_normKernel_eq_augmentationSubgroup (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    normKernelSubgroup (L ≃ₐ[K] L) (principalSubgroup k L) =
      augmentationSubgroup (L ≃ₐ[K] L) (principalSubgroup k L) σ :=
  le_antisymm (principal_normKernel_le_augmentationSubgroup σ hσ)
    (augmentationSubgroup_le_normKernelSubgroup σ)

/-- The actual principal-idele subgroup has vanishing cyclic Tate cohomology in degree minus one. -/
theorem principal_herbrandHMinusOne_subsingleton (σ : L ≃ₐ[K] L)
    (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    Subsingleton (HerbrandHMinusOne (L ≃ₐ[K] L) (principalSubgroup k L) σ) :=
  herbrandHMinusOne_subsingleton_of_normKernel_le_augmentationSubgroup σ
    (principal_normKernel_le_augmentationSubgroup σ hσ)

end FunctionField.IdeleGroup
