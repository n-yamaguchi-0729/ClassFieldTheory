/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.FieldIsomorphismRayNaturality
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.ReconstructedRayBaseChange

/-!
# Native field-isomorphism covariance of reconstructed functions

The specified field isomorphisms induce their own native ray maps by the
original degree-one reciprocity theorem. Commutation of the input ray maps
with those native group maps, and the actual place-restriction square,
therefore imply a restricted-product square by the proved local separation
argument. On the original principal kernels this is precisely equivariance
of the reconstructed functions. No function-equivariance hypothesis is used.
-/

@[expose] public section

universe u v w u₁ v₁ w₁ u₂ v₂ w₂

noncomputable section

open AlgebraicCurve LocalClassFieldTheory

namespace FunctionField.RayClass

private theorem ramificationIndex_eq_one_of_surjective
    {k : Type u} {K : Type v} {L : Type w} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional K L] (h : Function.Surjective (algebraMap K L))
    (w : Place k L) : w.ramificationIndex K = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨x, hx⟩ := h (π : L)
  have hne : x ≠ 0 := by
    intro hzero
    apply hπ.ne_zero
    apply Subtype.ext
    exact hx.symm.trans ((congrArg (algebraMap K L) hzero).trans (map_zero _))
  have hord : w.ord (algebraMap K L x) = 1 := by
    rw [hx]
    exact w.ord_coe_irreducible hπ
  have hle := w.ramificationIndex_le_ord (F := K) hne
    (show 0 < w.ord (algebraMap K L x) by rw [hord]; exact one_pos)
  have hpos := w.ramificationIndex_pos (F := K)
  rw [hord] at hle
  omega

variable {k₁ : Type u₁} {K₁ : Type v₁} {L₁ : Type w₁}
    {k₂ : Type u₂} {K₂ : Type v₂} {L₂ : Type w₂}
  [Field k₁] [Finite k₁] [Field K₁] [Field L₁]
  [Algebra k₁ K₁] [Algebra k₁ L₁]
  [Algebra (RatFunc k₁) K₁] [IsScalarTower k₁ (RatFunc k₁) K₁]
  [FunctionField k₁ K₁] [HasPrincipalDivisors k₁ K₁]
  [Algebra (RatFunc k₁) L₁] [IsScalarTower k₁ (RatFunc k₁) L₁]
  [FunctionField k₁ L₁] [HasPrincipalDivisors k₁ L₁]
  [Field k₂] [Finite k₂] [Field K₂] [Field L₂]
  [Algebra k₂ K₂] [Algebra k₂ L₂]
  [Algebra (RatFunc k₂) K₂] [IsScalarTower k₂ (RatFunc k₂) K₂]
  [FunctionField k₂ K₂] [HasPrincipalDivisors k₂ K₂]
  [Algebra (RatFunc k₂) L₂] [IsScalarTower k₂ (RatFunc k₂) L₂]
  [FunctionField k₂ L₂] [HasPrincipalDivisors k₂ L₂]
  (τ₁ : K₁ ≃ₐ[k₁] L₁) (τ₂ : K₂ ≃ₐ[k₂] L₂)
  (a₁ : SeparableClosure K₁ ≃+* SeparableClosure L₁)
  (a₂ : SeparableClosure K₂ ≃+* SeparableClosure L₂)
  (ha₁ : ∀ x : K₁, a₁ (algebraMap K₁ (SeparableClosure K₁) x) =
    algebraMap L₁ (SeparableClosure L₁) (τ₁ x))
  (ha₂ : ∀ x : K₂, a₂ (algebraMap K₂ (SeparableClosure K₂) x) =
    algebraMap L₂ (SeparableClosure L₂) (τ₂ x))
  (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
  (n₁ : Modulus k₁ L₁) (n₂ : Modulus k₂ L₂)
  (hm₁ : ∀ v, m₁ v ≤ 1) (hm₂ : ∀ v, m₂ v ≤ 1)
  (hn₁ : fieldIsoRayModulus τ₁ m₁ = n₁) (hn₂ : fieldIsoRayModulus τ₂ m₂ = n₂)
  (e : Place k₁ K₁ ≃ Place k₂ K₂) (eL : Place k₁ L₁ ≃ Place k₂ L₂)
  (γ : (localAbsoluteAbelianProfinite K₁ ⧸ artinRaySubgroup m₁) ≃*
    (localAbsoluteAbelianProfinite K₂ ⧸ artinRaySubgroup m₂))
  (Γ : (localAbsoluteAbelianProfinite L₁ ⧸ artinRaySubgroup n₁) ≃*
    (localAbsoluteAbelianProfinite L₂ ⧸ artinRaySubgroup n₂))
  (hclosure : ∀ v g,
    g ∈ (localRayAbsoluteArtin m₁ v).range.topologicalClosure ↔
      γ g ∈ (localRayAbsoluteArtin m₂ (e v)).range.topologicalClosure)
  (hdegree : ∀ g, rayAbelianDegree m₂ (γ g) = rayAbelianDegree m₁ g)
  (hclosureL : ∀ w g,
    g ∈ (localRayAbsoluteArtin n₁ w).range.topologicalClosure ↔
      Γ g ∈ (localRayAbsoluteArtin n₂ (eL w)).range.topologicalClosure)
  (hdegreeL : ∀ g, rayAbelianDegree n₂ (Γ g) = rayAbelianDegree n₁ g)
  (hb₁ : ∀ v : Place k₁ K₁, ∃ w : Place k₁ K₁, w ≠ v ∧ m₁ w ≠ 0)
  (hb₂ : ∀ v : Place k₂ K₂, ∃ w : Place k₂ K₂, w ≠ v ∧ m₂ w ≠ 0)
  (hbL₁ : ∀ v : Place k₁ L₁, ∃ w : Place k₁ L₁, w ≠ v ∧ n₁ w ≠ 0)
  (hbL₂ : ∀ v : Place k₂ L₂, ∃ w : Place k₂ L₂, w ≠ v ∧ n₂ w ≠ 0)

local notation "δ₁" => fieldIsoNativeRayHom τ₁ m₁ n₁ hm₁ hn₁ a₁ ha₁
local notation "δ₂" => fieldIsoNativeRayHom τ₂ m₂ n₂ hm₂ hn₂ a₂ ha₂
local notation "b₁" => fieldIsoRestrictedRayHom τ₁ m₁ n₁ hm₁ hn₁
local notation "b₂" => fieldIsoRestrictedRayHom τ₂ m₂ n₂ hm₂ hn₂
local notation "ρ" => reconstructedRestrictedRayEquiv m₁ m₂ e γ hclosure hdegree hb₁ hb₂
local notation "ρL" => reconstructedRestrictedRayEquiv n₁ n₂ eL Γ hclosureL hdegreeL hbL₁ hbL₂

variable
  (hplaces : ∀ w : Place k₁ L₁,
    fieldIsoPlaceRestrict τ₂ (eL w) = e (fieldIsoPlaceRestrict τ₁ w))
  (hnative : ∀ g,
    Γ (fieldIsoNativeRayHom τ₁ m₁ n₁ hm₁ hn₁ a₁ ha₁ g) =
      fieldIsoNativeRayHom τ₂ m₂ n₂ hm₂ hn₂ a₂ ha₂ (γ g))

include hplaces hnative in
/-- The original native conjugation square forces the actual
restricted-product square of the reconstructed multiplication. -/
theorem reconstructedRestrictedRayEquiv_fieldIso :
    MonoidHom.comp (MulEquiv.toMonoidHom ρL) b₁ =
      MonoidHom.comp b₂ (MulEquiv.toMonoidHom ρ) := by
  let : Algebra K₁ L₁ := τ₁.toRingHom.toAlgebra
  have : IsScalarTower k₁ K₁ L₁ :=
    IsScalarTower.of_algebraMap_eq (fun x => (τ₁.commutes x).symm)
  let f₁ := fieldIsoAsAlgEquiv τ₁.toRingEquiv
  have : FiniteDimensional K₁ L₁ :=
    FiniteDimensional.of_surjective f₁.toLinearMap f₁.surjective
  let : Algebra K₂ L₂ := τ₂.toRingHom.toAlgebra
  have : IsScalarTower k₂ K₂ L₂ :=
    IsScalarTower.of_algebraMap_eq (fun x => (τ₂.commutes x).symm)
  let f₂ := fieldIsoAsAlgEquiv τ₂.toRingEquiv
  have : FiniteDimensional K₂ L₂ :=
    FiniteDimensional.of_surjective f₂.toLinearMap f₂.surjective
  apply reconstructedRestrictedRayEquiv_baseChange_of_modulus_eq
    m₁ m₂ n₁ n₂ hm₁ hm₂ hn₁ hn₂ e eL γ Γ hclosure hdegree hclosureL hdegreeL
    hb₁ hb₂ hbL₁ hbL₂ hplaces
    (fun w => (ramificationIndex_eq_one_of_surjective τ₁.surjective w).trans
      (ramificationIndex_eq_one_of_surjective τ₂.surjective (eL w)).symm)
  apply MonoidHom.ext
  intro x
  change restrictedProductAbsoluteArtin n₂ (ρL (b₁ x)) =
    restrictedProductAbsoluteArtin n₂ (b₂ (ρ x))
  rw [reconstructedRestrictedRayEquiv_artin,
    fieldIsoNativeRayHom_artin τ₁ m₁ n₁ hm₁ hn₁ a₁ ha₁ x,
    hnative, ← reconstructedRestrictedRayEquiv_artin,
    fieldIsoNativeRayHom_artin τ₂ m₂ n₂ hm₂ hn₂ a₂ ha₂ (ρ x)]

variable (hz₁ : m₁ ≠ 0) (hz₂ : m₂ ≠ 0) (hzL₁ : n₁ ≠ 0) (hzL₂ : n₂ ≠ 0)

include hplaces hnative in
/-- Every original function is equivariant under the specified actual
field isomorphisms, as a consequence of native ray covariance. The zero
extension remains the same reconstructed multiplicative map. -/
theorem reconstructedRayFunction_fieldIso (x : K₁) :
    let baseFunction : K₁ ≃* K₂ :=
      reconstructedRayFunction m₁ m₂ e γ hclosure hdegree hb₁ hb₂ hz₁ hz₂
    let extensionFunction : L₁ ≃* L₂ :=
      reconstructedRayFunction n₁ n₂ eL Γ hclosureL hdegreeL hbL₁ hbL₂ hzL₁ hzL₂
    extensionFunction (τ₁ x) = τ₂ (baseFunction x) := by
  intro baseFunction extensionFunction
  let : Algebra K₁ L₁ := τ₁.toRingHom.toAlgebra
  have : IsScalarTower k₁ K₁ L₁ :=
    IsScalarTower.of_algebraMap_eq (fun x => (τ₁.commutes x).symm)
  let f₁ := fieldIsoAsAlgEquiv τ₁.toRingEquiv
  have : FiniteDimensional K₁ L₁ :=
    FiniteDimensional.of_surjective f₁.toLinearMap f₁.surjective
  let : Algebra K₂ L₂ := τ₂.toRingHom.toAlgebra
  have : IsScalarTower k₂ K₂ L₂ :=
    IsScalarTower.of_algebraMap_eq (fun x => (τ₂.commutes x).symm)
  let f₂ := fieldIsoAsAlgEquiv τ₂.toRingEquiv
  have : FiniteDimensional K₂ L₂ :=
    FiniteDimensional.of_surjective f₂.toLinearMap f₂.surjective
  have hcoherence := reconstructedRestrictedRayEquiv_fieldIso
    τ₁ τ₂ a₁ a₂ ha₁ ha₂ m₁ m₂ n₁ n₂ hm₁ hm₂ hn₁ hn₂ e eL γ Γ
    hclosure hdegree hclosureL hdegreeL hb₁ hb₂ hbL₁ hbL₂ hplaces hnative
  have hartin : (restrictedProductAbsoluteArtin n₂).comp
      (MonoidHom.comp (MulEquiv.toMonoidHom ρL) b₁) =
      (restrictedProductAbsoluteArtin n₂).comp
        (MonoidHom.comp b₂ (MulEquiv.toMonoidHom ρ)) :=
    congrArg (fun f : RayRestrictedProduct m₁ →* RayRestrictedProduct n₂ =>
      (restrictedProductAbsoluteArtin n₂).comp f) hcoherence
  exact reconstructedRayFunction_baseChange_of_modulus_eq
    m₁ m₂ n₁ n₂ hm₁ hm₂ hn₁ hn₂ e eL γ Γ hclosure hdegree hclosureL hdegreeL
    hb₁ hb₂ hbL₁ hbL₂ hplaces
    (fun w => (ramificationIndex_eq_one_of_surjective τ₁.surjective w).trans
      (ramificationIndex_eq_one_of_surjective τ₂.surjective (eL w)).symm)
    hartin hz₁ hz₂ x

end FunctionField.RayClass
