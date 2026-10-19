/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_genusFF_eq_of_algEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Places.Rational.Basic

/-!
The function-field genus is invariant under an algebra equivalence.
Transport of places and repartitions identifies the defining quotient spaces.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusFF_eq_of_algEquiv

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

open WithZero

variable {K : Type*} [Field K]

section Congr
variable {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
variable (e : F₁ ≃ₐ[K] F₂)

namespace Place
open scoped _root_.AlgebraicCurve.Place in
private def _root_.AlgebraicCurve.Place.congr (v : Place K F₁) : Place K F₂ :=
  Place.congrRingEquiv e.toRingEquiv e.commutes v

end Place
open _root_.AlgebraicCurve
open scoped _root_.AlgebraicCurve.Place in
theorem Place.congr_toValuationSubring (v : Place K F₁) :
    (v.congr e).toValuationSubring = v.toValuationSubring.comap e.symm := rfl

namespace Place
open scoped _root_.AlgebraicCurve.Place in
private theorem _root_.AlgebraicCurve.Place.mem_congr_iff (v : Place K F₁) (x : F₁) :
    e x ∈ (v.congr e).toValuationSubring ↔ x ∈ v.toValuationSubring := by
  change e.symm (e x) ∈ v.toValuationSubring ↔ _
  rw [e.symm_apply_apply]

end Place
open _root_.AlgebraicCurve
open scoped _root_.AlgebraicCurve.Place in
theorem Place.congr_symm_congr (v : Place K F₁) :
    (v.congr e).congr e.symm = v := by
  refine Place.ext (SetLike.ext fun x => ?_)
  change (e.symm.symm : F₁ →+* F₂) x ∈ (v.congr e).toValuationSubring ↔ x ∈ v.toValuationSubring
  simp only [AlgEquiv.symm_symm]
  exact v.mem_congr_iff e x

open scoped _root_.AlgebraicCurve.Place in
theorem Place.congr_congr_symm (w : Place K F₂) :
    (w.congr e.symm).congr e = w := by
  have h := Place.congr_symm_congr e.symm w
  simpa only [AlgEquiv.symm_symm] using h

open scoped _root_.AlgebraicCurve.Place in
theorem Place.congr_adicValuation_le_one_iff (v : Place K F₁) (x : F₁) :
    (v.congr e).adicValuation (e x) ≤ 1 ↔ v.adicValuation x ≤ 1 := by
  rw [← Place.mem_iff_adicValuation_le_one, ← Place.mem_iff_adicValuation_le_one,
    Place.mem_congr_iff]

/--
Transport a family of field elements along the algebra equivalence and its induced place
equivalence.
-/
def piMap : (Place K F₁ → F₁) →+* (Place K F₂ → F₂) :=
  RingHom.pi fun w => (e : F₁ →+* F₂).comp (Pi.evalRingHom _ (w.congr e.symm))

theorem piMap_apply (α : Place K F₁ → F₁) (w : Place K F₂) :
    piMap e α w = e (α (w.congr e.symm)) := rfl

theorem piMap_symm_piMap (α : Place K F₁ → F₁) :
    piMap e.symm (piMap e α) = α :=
  funext fun v => by
    simp only [piMap_apply, AlgEquiv.symm_symm, Place.congr_symm_congr]
    exact e.symm_apply_apply _

theorem piMap_algebraMap (c : F₁) :
    piMap e (algebraMap F₁ (Place K F₁ → F₁) c) = algebraMap F₂ _ (e c) :=
  funext fun _ => rfl

theorem piMap_mem_repartitions :
    ∀ α ∈ (repartitions K F₁ : Set _), piMap e α ∈ repartitions K F₂ := by
  intro α hα
  change α ∈ (repartitions K F₁ : Subalgebra F₁ _) at hα
  induction hα using Algebra.adjoin_induction with
  | mem β hβ =>
    refine Algebra.subset_adjoin ?_
    have hsub : {w : Place K F₂ | ¬w.adicValuation (piMap e β w) ≤ 1}
        ⊆ (Place.congr e) '' {v | ¬v.adicValuation (β v) ≤ 1} := by
      intro w hw
      refine ⟨w.congr e.symm, fun hle => hw ?_, Place.congr_congr_symm e w⟩
      show w.adicValuation (piMap e β w) ≤ 1
      rw [piMap_apply]
      have key := Place.congr_adicValuation_le_one_iff e (w.congr e.symm)
        (β (w.congr e.symm))
      rw [Place.congr_congr_symm e w] at key
      exact key.mpr hle
    exact (hβ.image _).subset hsub
  | algebraMap c => rw [piMap_algebraMap]; exact (repartitions K F₂).algebraMap_mem _
  | add x y _ _ hx' hy' => rw [map_add]; exact add_mem hx' hy'
  | mul x y _ _ hx' hy' => rw [map_mul]; exact mul_mem hx' hy'

/-- Transport repartitions along the algebra equivalence as a linear map. -/
def repLinMap : ↥(repartitions K F₁) →ₗ[K] ↥(repartitions K F₂) where
  toFun α := ⟨piMap e α, piMap_mem_repartitions e α α.2⟩
  map_add' α β := Subtype.ext (map_add _ _ _)
  map_smul' c α := by
    apply Subtype.ext
    ext w
    simp only [RingHom.id_apply, Subalgebra.coe_smul, piMap_apply, Pi.smul_apply,
      _root_.map_smul]

theorem repLinMap_apply_coe (α : ↥(repartitions K F₁)) :
    ((repLinMap e α : repartitions K F₂) : Place K F₂ → F₂) = piMap e ↑α := rfl

theorem repLinMap_symm_repLinMap (α : ↥(repartitions K F₁)) :
    repLinMap e.symm (repLinMap e α) = α :=
  Subtype.ext (piMap_symm_piMap e _)

theorem repLinMap_mem_repartitionsOf_zero (α : ↥(repartitions K F₁))
    (hα : α ∈ repartitionsOf (0 : Divisor K F₁)) :
    repLinMap e α ∈ repartitionsOf (0 : Divisor K F₂) := by
  intro w
  simp only [Finsupp.coe_zero, Pi.zero_apply, exp_zero, repLinMap_apply_coe, piMap_apply]
  have key := Place.congr_adicValuation_le_one_iff e (w.congr e.symm)
    ((α : Place K F₁ → F₁) (w.congr e.symm))
  rw [Place.congr_congr_symm e w] at key
  rw [key]
  simpa only [Finsupp.coe_zero, Pi.zero_apply, exp_zero] using hα (w.congr e.symm)

theorem repLinMap_mem_principal (α : ↥(repartitions K F₁))
    (hα : α ∈ principalRepartitions K F₁) :
    repLinMap e α ∈ principalRepartitions K F₂ := by
  rw [mem_principalRepartitions_iff] at hα ⊢
  obtain ⟨f, hf⟩ := hα
  refine ⟨e f, funext fun w => ?_⟩
  rw [repLinMap_apply_coe, piMap_apply, hf]

end Congr

end AlgebraicCurve

open _root_.AlgebraicCurve

open _root_.AlgebraicCurves.Cohomology.RiemannRoch.Proofs in
theorem _root_.AlgebraicCurve.genusFF_eq_of_algEquiv
    {K F₁ F₂ : Type*} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
    (e : F₁ ≃ₐ[K] F₂) :
    genusFF K F₁ = genusFF K F₂ := by
  let eRep : ↥(repartitions K F₁) ≃ₗ[K] ↥(repartitions K F₂) :=
    { GenusFF_eq_of_algEquiv.AlgebraicCurve.repLinMap e with
      invFun := GenusFF_eq_of_algEquiv.AlgebraicCurve.repLinMap e.symm
      left_inv := GenusFF_eq_of_algEquiv.AlgebraicCurve.repLinMap_symm_repLinMap e
      right_inv := fun β => by
        change GenusFF_eq_of_algEquiv.AlgebraicCurve.repLinMap e
          (GenusFF_eq_of_algEquiv.AlgebraicCurve.repLinMap e.symm β) = β
        simpa only [AlgEquiv.symm_symm] using
          GenusFF_eq_of_algEquiv.AlgebraicCurve.repLinMap_symm_repLinMap e.symm β }
  have hmap :
      (repartitionsOf (0 : Divisor K F₁) ⊔ principalRepartitions K F₁).map
        (eRep : ↥(repartitions K F₁) →ₗ[K] ↥(repartitions K F₂))
      = repartitionsOf (0 : Divisor K F₂) ⊔ principalRepartitions K F₂ := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.map_sup, sup_le_iff]
      constructor
      · rw [Submodule.map_le_iff_le_comap]
        exact fun α hα => Submodule.mem_sup_left
          (GenusFF_eq_of_algEquiv.AlgebraicCurve.repLinMap_mem_repartitionsOf_zero e α hα)
      · rw [Submodule.map_le_iff_le_comap]
        exact fun α hα => Submodule.mem_sup_right
          (GenusFF_eq_of_algEquiv.AlgebraicCurve.repLinMap_mem_principal e α hα)
    · intro β hβ
      rw [Submodule.mem_map]
      refine ⟨eRep.symm β, ?_, eRep.apply_symm_apply β⟩
      change GenusFF_eq_of_algEquiv.AlgebraicCurve.repLinMap e.symm β ∈ _
      rcases Submodule.mem_sup.mp hβ with ⟨β₀, hβ₀, βp, hβp, rfl⟩
      rw [map_add]
      exact Submodule.add_mem_sup
        (GenusFF_eq_of_algEquiv.AlgebraicCurve.repLinMap_mem_repartitionsOf_zero e.symm β₀ hβ₀)
        (GenusFF_eq_of_algEquiv.AlgebraicCurve.repLinMap_mem_principal e.symm βp hβp)
  exact (Submodule.Quotient.equiv _ _ eRep hmap).finrank_eq
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusFF_eq_of_algEquiv
end ProofImplementation
