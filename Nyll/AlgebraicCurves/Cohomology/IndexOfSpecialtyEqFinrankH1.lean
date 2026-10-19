/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.MemAdeleSpaceIffMemRepartitions

/-!
The index of specialty is the dimension of first adelic cohomology.
The adelic and repartition models are identified by their common bounded families.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.IndexOfSpecialty_eq_finrank_H1

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adeleSpace_eq_restrictScalars_repartitions [HasPrincipalDivisors K F] :
    adeleSpace K F = (Subalgebra.toSubmodule (repartitions K F)).restrictScalars K := by
  ext α
  exact mem_adeleSpace_iff_mem_repartitions

/-- Identify the adelic space with repartitions by their common underlying bounded families. -/
noncomputable def adeleSpaceEquivRepartitions [HasPrincipalDivisors K F] :
    ↥(adeleSpace K F) ≃ₗ[K] ↥(repartitions K F) where
  toFun α := ⟨α, mem_adeleSpace_iff_mem_repartitions.mp α.2⟩
  invFun α := ⟨α, mem_adeleSpace_iff_mem_repartitions.mpr α.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

end AlgebraicCurve

open _root_.AlgebraicCurves.Cohomology.Proofs in
open _root_.AlgebraicCurve IndexOfSpecialty_eq_finrank_H1.AlgebraicCurve
  Mem_adeleSpace_iff_mem_repartitions.AlgebraicCurve WithZero in
theorem _root_.AlgebraicCurve.indexOfSpecialty_eq_finrank_H1 {K F : Type*} [Field K] [Field F]
    [Algebra K F] [HasPrincipalDivisors K F] (D : Divisor K F) :
    indexOfSpecialty D = Module.finrank K (H1 D) := by
  let e := adeleSpaceEquivRepartitions (K := K) (F := F)
  have hmap : (adeleBddPrincipal K F D).map (e : ↥(adeleSpace K F) →ₗ[K] ↥(repartitions K F))
      = repartitionsOf D ⊔ principalRepartitions K F := by
    rw [Submodule.map_sup]
    congr 1
    · ext α
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      · rintro ⟨β, hβ, rfl⟩; exact hβ
      · intro hα; exact ⟨e.symm α, hα, e.apply_symm_apply α⟩
    · ext α
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      · rintro ⟨β, hβ, rfl⟩; exact mem_principalRepartitions_iff_coe_mem_globalSub.mpr hβ
      · intro hα
        exact ⟨e.symm α, mem_principalRepartitions_iff_coe_mem_globalSub.mp hα, e.apply_symm_apply
          α⟩
  rw [indexOfSpecialty_eq]
  exact LinearEquiv.finrank_eq (Submodule.Quotient.equiv _ _ e hmap)
end AlgebraicCurves.Cohomology.Proofs.IndexOfSpecialty_eq_finrank_H1
end ProofImplementation
