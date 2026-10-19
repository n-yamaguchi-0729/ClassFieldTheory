/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_Mumford_bijective_kerMapBaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.Covers.MumfordTruncation
import Nyll.AlgebraicCurves.Cohomology.Cech.BaseChange.TwoChartCechMumfordBijectiveCokerMapBaseChange
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
Bijectivity of kernel base change in the finite-presentation construction for a Cech differential.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_Mumford_bijective_kerMapBaseChange

noncomputable section

open scoped TensorProduct

universe u

namespace TwoChartCech
open _root_.TwoChartCech
namespace Mumford
open _root_.TwoChartCech.Mumford
open _root_.TwoChartCech.Mumford
open _root_.TwoChartCech

open _root_.AlgebraicCurves.Cohomology.Cech.Proofs
open TwoChartCech_Mumford_bijective_cokerMapBaseChange.TwoChartCech.Mumford

variable {R : Type u} [CommRing R]
variable {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
variable (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
variable (A : Type u) [CommRing A] [Algebra R A]

theorem subtype_baseChange_injective [Module.Flat R C1] :
    Function.Injective ((K0 d).subtype.baseChange A) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_injective_of_exact_of_flat (d.coprod (lift d))
    (surjective_coprod d) _ (K0 d).subtype_injective (LinearMap.exact_subtype_ker_map _) A

theorem kerMapBaseChange_injective [Module.Flat R C1] :
    Function.Injective (kerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) A) := by
  rintro ⟨z, hz⟩ ⟨z', hz'⟩ hzz'
  apply Subtype.ext
  apply subtype_baseChange_injective d A
  apply (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)).injective
  rw [prodRight_subtype_baseChange d A z, prodRight_subtype_baseChange d A z']
  have h1 : ((dK d).baseChange A) z = 0 := hz
  have h2 : ((dK d).baseChange A) z' = 0 := hz'
  rw [h1, h2]
  exact congrArg (·, (0 : A ⊗[R] (Fin (rank d) → R))) (congrArg Subtype.val hzz')

theorem kerMapBaseChange_surjective :
    Function.Surjective (kerMapBaseChange (dK d) d (ι0 d) (ι1 d) (comm d) A) := by
  rintro ⟨w, hw⟩
  set w' : A ⊗[R] (C0 × (Fin (rank d) → R)) :=
    ((LinearMap.inl R C0 (Fin (rank d) → R)).baseChange A) w with hw'def
  have hker : ((d.coprod (lift d)).baseChange A) w' = 0 := by
    rw [hw'def, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, LinearMap.coprod_inl]
    exact hw
  obtain ⟨z, hz⟩ := (mem_range_subtype_baseChange d A w').mp hker
  have hpr : (TensorProduct.prodRight R A A C0 (Fin (rank d) → R)) w' = (w, 0) := by
    rw [prodRight_apply_eq_baseChange, hw'def, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      LinearMap.fst_comp_inl R C0 (Fin (rank d) → R),
      LinearMap.snd_comp_inl R C0 (Fin (rank d) → R),
      LinearMap.baseChange_id, LinearMap.baseChange_zero, LinearMap.id_apply,
      LinearMap.zero_apply]
  have hpair : (((ι0 d).baseChange A) z, ((dK d).baseChange A) z) = (w, 0) := by
    rw [← prodRight_subtype_baseChange d A z, hz, hpr]
  refine ⟨⟨z, (Prod.ext_iff.mp hpair).2⟩, ?_⟩
  exact Subtype.ext (Prod.ext_iff.mp hpair).1

end TwoChartCech.Mumford

open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
open _root_.TwoChartCech.Mumford
  TwoChartCech_Mumford_bijective_kerMapBaseChange.TwoChartCech.Mumford in
theorem _root_.TwoChartCech.Mumford.bijective_kerMapBaseChange
    {R : Type u} [CommRing R]
    {C0 C1 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1] [Module.Flat
      R C1]
    (d : C0 →ₗ[R] C1) [Module.Finite R (C1 ⧸ LinearMap.range d)]
    (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective
      (TwoChartCech.kerMapBaseChange (TwoChartCech.Mumford.dK d) d (TwoChartCech.Mumford.ι0 d)
        (TwoChartCech.Mumford.ι1 d) (TwoChartCech.Mumford.comm d) A) :=
  ⟨kerMapBaseChange_injective d A, kerMapBaseChange_surjective d A⟩

end
end AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartCech_Mumford_bijective_kerMapBaseChange
end ProofImplementation
