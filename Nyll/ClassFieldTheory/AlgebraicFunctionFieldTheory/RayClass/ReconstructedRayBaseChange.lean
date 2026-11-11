/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayBaseChangeCoherence
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.LocalRayReconstruction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayReconstruction
public import Nyll.ClassFieldTheory.AlgebraicFunctionFieldTheory.RayClass.RestrictedRayTower

/-!
# Reconstructed native ray kernels under literal finite extension

The local factors reconstructed from the original ray quotient maps preserve
normalized orders. The original Artin square therefore determines the entire
restricted-product square by finite-support separation. Restricting that
proved square gives the equality of the actual Artin-kernel transitions.

The upper moduli are allowed to be the directly pulled-back original moduli.
Their equality with the iterated pullbacks is applied explicitly, which keeps
the same native objects through a finite constant-field tower.
-/

@[expose] public section

universe u₁ v₁ w₁ u₂ v₂ w₂

noncomputable section

open AlgebraicCurve LocalClassFieldTheory

namespace FunctionField.RayClass

variable {k₁ : Type u₁} {K₁ : Type v₁} {L₁ : Type w₁}
    {k₂ : Type u₂} {K₂ : Type v₂} {L₂ : Type w₂}
    [Field k₁] [Finite k₁] [Field K₁] [Field L₁]
    [Algebra k₁ K₁] [Algebra k₁ L₁] [Algebra K₁ L₁]
    [IsScalarTower k₁ K₁ L₁] [FiniteDimensional K₁ L₁]
    [Algebra (RatFunc k₁) K₁] [IsScalarTower k₁ (RatFunc k₁) K₁]
    [FunctionField k₁ K₁] [HasPrincipalDivisors k₁ K₁]
    [Algebra (RatFunc k₁) L₁] [IsScalarTower k₁ (RatFunc k₁) L₁]
    [FunctionField k₁ L₁] [HasPrincipalDivisors k₁ L₁]
    [Field k₂] [Finite k₂] [Field K₂] [Field L₂]
    [Algebra k₂ K₂] [Algebra k₂ L₂] [Algebra K₂ L₂]
    [IsScalarTower k₂ K₂ L₂] [FiniteDimensional K₂ L₂]
    [Algebra (RatFunc k₂) K₂] [IsScalarTower k₂ (RatFunc k₂) K₂]
    [FunctionField k₂ K₂] [HasPrincipalDivisors k₂ K₂]
    [Algebra (RatFunc k₂) L₂] [IsScalarTower k₂ (RatFunc k₂) L₂]
    [FunctionField k₂ L₂] [HasPrincipalDivisors k₂ L₂]
    (m₁ : Modulus k₁ K₁) (m₂ : Modulus k₂ K₂)
    (n₁ : Modulus k₁ L₁) (n₂ : Modulus k₂ L₂)
    (hm₁ : ∀ v, m₁ v ≤ 1) (hm₂ : ∀ v, m₂ v ≤ 1)
    (hn₁ : rayModulusBaseChange L₁ m₁ = n₁)
    (hn₂ : rayModulusBaseChange L₂ m₂ = n₂)
    (e : Place k₁ K₁ ≃ Place k₂ K₂)
    (eL : Place k₁ L₁ ≃ Place k₂ L₂)
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
    (hboundary₁ : ∀ v : Place k₁ K₁, ∃ w : Place k₁ K₁, w ≠ v ∧ m₁ w ≠ 0)
    (hboundary₂ : ∀ v : Place k₂ K₂, ∃ w : Place k₂ K₂, w ≠ v ∧ m₂ w ≠ 0)
    (hboundaryL₁ : ∀ v : Place k₁ L₁, ∃ w : Place k₁ L₁, w ≠ v ∧ n₁ w ≠ 0)
    (hboundaryL₂ : ∀ v : Place k₂ L₂, ∃ w : Place k₂ L₂, w ≠ v ∧ n₂ w ≠ 0)

local notation "ρ" => reconstructedRestrictedRayEquiv m₁ m₂ e γ
  hclosure hdegree hboundary₁ hboundary₂
local notation "ρL" => reconstructedRestrictedRayEquiv n₁ n₂ eL Γ
  hclosureL hdegreeL hboundaryL₁ hboundaryL₂
local notation "η" => reconstructedRayKernelEquiv m₁ m₂ e γ
  hclosure hdegree hboundary₁ hboundary₂
local notation "ηL" => reconstructedRayKernelEquiv n₁ n₂ eL Γ
  hclosureL hdegreeL hboundaryL₁ hboundaryL₂
local notation "b₁" => MonoidHom.comp (MulEquiv.toMonoidHom (rayModulusCongr hn₁))
  (restrictedRayBaseChange (L := L₁) m₁ hm₁)
local notation "b₂" => MonoidHom.comp (MulEquiv.toMonoidHom (rayModulusCongr hn₂))
  (restrictedRayBaseChange (L := L₂) m₂ hm₂)

variable
    (hplaces : ∀ w : Place k₁ L₁, (eL w).restrict K₂ = e (w.restrict K₁))
    (hindex : ∀ w : Place k₁ L₁,
      w.ramificationIndex K₁ = (eL w).ramificationIndex K₂)
    (hartin : (restrictedProductAbsoluteArtin n₂).comp
        ((reconstructedRestrictedRayEquiv n₁ n₂ eL Γ
          hclosureL hdegreeL hboundaryL₁ hboundaryL₂).toMonoidHom.comp
          ((rayModulusCongr hn₁).toMonoidHom.comp
            (restrictedRayBaseChange (L := L₁) m₁ hm₁))) =
      (restrictedProductAbsoluteArtin n₂).comp
        (((rayModulusCongr hn₂).toMonoidHom.comp
          (restrictedRayBaseChange (L := L₂) m₂ hm₂)).comp
          (reconstructedRestrictedRayEquiv m₁ m₂ e γ
            hclosure hdegree hboundary₁ hboundary₂).toMonoidHom))

include hplaces hindex hartin

/-- Original reciprocity and the actual place-restriction square force
coherence of the reconstructed local maps on the entire restricted product. -/
theorem reconstructedRestrictedRayEquiv_baseChange_of_modulus_eq :
    (ρL).toMonoidHom.comp b₁ = (b₂).comp (ρ).toMonoidHom := by
  subst n₁
  subst n₂
  apply restrictedRayEquiv_baseChange_of_artin_square m₁ m₂ hm₁ hm₂ e eL hplaces
    (fun v => localRayEquivOfClosure m₁ v m₂ (e v) γ
      (hclosure v) hdegree (hboundary₁ v) (hboundary₂ (e v)))
    (fun w => localRayEquivOfClosure _ w _ (eL w) Γ
      (hclosureL w) hdegreeL (hboundaryL₁ w) (hboundaryL₂ (eL w)))
    (fun v a => localRayFactorOrder_map m₁ v m₂ (e v) γ
      (hclosure v) hdegree (hboundary₁ v) (hboundary₂ (e v)) a)
    (fun w a => localRayFactorOrder_map _ w _ (eL w) Γ
      (hclosureL w) hdegreeL (hboundaryL₁ w) (hboundaryL₂ (eL w)) a)
    hindex hboundary₂
  exact hartin

/-- The actual Artin-kernel arrows commute with their literal finite-field
transitions as a consequence of the proved restricted-product square. -/
theorem reconstructedRayKernelEquiv_baseChange_of_modulus_eq
    (a : (restrictedProductAbsoluteArtin m₁).ker) :
    ηL (principalArtinKernelCongr hn₁ (principalArtinKernelBaseChange (L := L₁) m₁ hm₁ a)) =
      principalArtinKernelCongr hn₂ (principalArtinKernelBaseChange (L := L₂) m₂ hm₂ (η a)) := by
  have h := reconstructedRestrictedRayEquiv_baseChange_of_modulus_eq
    m₁ m₂ n₁ n₂ hm₁ hm₂ hn₁ hn₂ e eL γ Γ hclosure hdegree hclosureL hdegreeL
    hboundary₁ hboundary₂ hboundaryL₁ hboundaryL₂ hplaces hindex hartin
  apply Subtype.ext
  rw [reconstructedRayKernelEquiv_coe, principalArtinKernelCongr_coe,
    principalArtinKernelCongr_coe]
  exact DFunLike.congr_fun h a.val

variable (hz₁ : m₁ ≠ 0) (hz₂ : m₂ ≠ 0)

local notation "hzL₁" => Eq.mp (congrArg (fun m => m ≠ 0) hn₁)
  (rayModulusBaseChange_ne_zero (L := L₁) m₁ hz₁)
local notation "hzL₂" => Eq.mp (congrArg (fun m => m ≠ 0) hn₂)
  (rayModulusBaseChange_ne_zero (L := L₂) m₂ hz₂)
local notation "φ" => reconstructedRayFunctionUnits m₁ m₂ e γ
  hclosure hdegree hboundary₁ hboundary₂ hz₁ hz₂
local notation "φL" => reconstructedRayFunctionUnits n₁ n₂ eL Γ
  hclosureL hdegreeL hboundaryL₁ hboundaryL₂ hzL₁ hzL₂

/-- The proved restricted-product square retains the actual coefficient
map on every original function unit. This applies to a degree-one field
map as well as to a proper finite field extension. -/
theorem reconstructedRayFunctionUnits_baseChange_of_modulus_eq (x : K₁ˣ) :
    φL (Units.map (algebraMap K₁ L₁).toMonoidHom x) =
      Units.map (algebraMap K₂ L₂).toMonoidHom (φ x) := by
  have hcoherence := reconstructedRestrictedRayEquiv_baseChange_of_modulus_eq
    m₁ m₂ n₁ n₂ hm₁ hm₂ hn₁ hn₂ e eL γ Γ hclosure hdegree hclosureL hdegreeL
    hboundary₁ hboundary₂ hboundaryL₁ hboundaryL₂ hplaces hindex hartin
  have hlower := reconstructedRayFunctionUnits_principal m₁ m₂ e γ
    hclosure hdegree hboundary₁ hboundary₂ hz₁ hz₂ x
  have hupper := reconstructedRayFunctionUnits_principal n₁ n₂ eL Γ
    hclosureL hdegreeL hboundaryL₁ hboundaryL₂ hzL₁ hzL₂
    (Units.map (algebraMap K₁ L₁).toMonoidHom x)
  simp only [principalRestrictedArtinKernelEquiv_coe] at hlower hupper
  have hbase₁ (y : K₁ˣ) : b₁ (principalToRayRestrictedProduct m₁ y) =
      principalToRayRestrictedProduct n₁ (Units.map (algebraMap K₁ L₁).toMonoidHom y) := by
    change rayModulusCongr hn₁
      (restrictedRayBaseChange (L := L₁) m₁ hm₁ (principalToRayRestrictedProduct m₁ y)) = _
    rw [restrictedRayBaseChange_principal, rayModulusCongr_principal]
    rfl
  have hbase₂ (y : K₂ˣ) : b₂ (principalToRayRestrictedProduct m₂ y) =
      principalToRayRestrictedProduct n₂ (Units.map (algebraMap K₂ L₂).toMonoidHom y) := by
    change rayModulusCongr hn₂
      (restrictedRayBaseChange (L := L₂) m₂ hm₂ (principalToRayRestrictedProduct m₂ y)) = _
    rw [restrictedRayBaseChange_principal, rayModulusCongr_principal]
    rfl
  apply (principalRestrictedArtinKernelEquiv n₂ hzL₂).injective
  apply Subtype.ext
  simp only [principalRestrictedArtinKernelEquiv_coe]
  calc
    principalToRayRestrictedProduct n₂ (φL (Units.map (algebraMap K₁ L₁).toMonoidHom x)) =
        ρL (principalToRayRestrictedProduct n₁
          (Units.map (algebraMap K₁ L₁).toMonoidHom x)) := hupper
    _ = ρL (b₁ (principalToRayRestrictedProduct m₁ x)) := congrArg ρL (hbase₁ x).symm
    _ = b₂ (ρ (principalToRayRestrictedProduct m₁ x)) :=
      DFunLike.congr_fun hcoherence (principalToRayRestrictedProduct m₁ x)
    _ = b₂ (principalToRayRestrictedProduct m₂ (φ x)) := congrArg b₂ hlower.symm
    _ = principalToRayRestrictedProduct n₂ (Units.map (algebraMap K₂ L₂).toMonoidHom (φ x)) :=
      hbase₂ (φ x)

local notation "φ₀" => reconstructedRayFunction m₁ m₂ e γ
  hclosure hdegree hboundary₁ hboundary₂ hz₁ hz₂
local notation "φL₀" => reconstructedRayFunction n₁ n₂ eL Γ
  hclosureL hdegreeL hboundaryL₁ hboundaryL₂ hzL₁ hzL₂

/-- The same coefficient square holds on the entire original fields,
including zero, without changing the reconstructed multiplicative maps. -/
theorem reconstructedRayFunction_baseChange_of_modulus_eq (x : K₁) :
    φL₀ (algebraMap K₁ L₁ x) = algebraMap K₂ L₂ (φ₀ x) := by
  rcases GroupWithZero.eq_zero_or_unit x with rfl | ⟨u, rfl⟩
  · simp only [map_zero]
  · change φL₀ ((Units.map (algebraMap K₁ L₁).toMonoidHom u : L₁ˣ) : L₁) =
      algebraMap K₂ L₂ (φ₀ (u : K₁))
    rw [reconstructedRayFunction_apply_units, reconstructedRayFunction_apply_units]
    exact congrArg (fun z : L₂ˣ => (z : L₂))
      (reconstructedRayFunctionUnits_baseChange_of_modulus_eq
        m₁ m₂ n₁ n₂ hm₁ hm₂ hn₁ hn₂ e eL γ Γ hclosure hdegree hclosureL hdegreeL
        hboundary₁ hboundary₂ hboundaryL₁ hboundaryL₂ hplaces hindex hartin hz₁ hz₂ u)

end FunctionField.RayClass
